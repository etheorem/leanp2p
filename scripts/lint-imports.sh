#!/usr/bin/env bash
# The import lint: a build gate over the package tree.
#
# Rule 1, the group chain (ARCHITECTURE §2): the groups run
# cli → libp2p → net → crypto → codec → base. A module imports groups
# strictly to its right, plus its own group. Membership decides on the
# first segment of the imported module name. `Libp2p` is the one prefix
# match on the whole dotted name, so `Libp2p.Security.Payload` counts
# as libp2p. Names outside the table (`Lean`, `Init`, `Std`) are
# external, and the lint ignores them.
#
# Rule 2, no libp2p below libp2p (ARCHITECTURE §2, PRINCIPLES 4.3): a
# .lean file under base, codec, crypto, or net must not contain the
# token libp2p, in any case. Docstring mentions count. The rule keeps
# the packages reusable by other projects.
#
# Rule 3, within groups, downward only (ARCHITECTURE §2, §3.1): a file
# under `packages/<group>/<leaf>/` belongs to that leaf. An import of
# leaf M by a file of leaf L is allowed when M is L itself or M's rank
# is below L's; imports point downward along the chain arrows of §2:
# net streams < yamux; codec varint = snappy < proto = multiformats;
# crypto pure = backend < the Crypto facade; libp2p identity < core <
# security = mux < negotiate < host < protocols. Siblings have no
# edge, so an equal-rank import is a violation either way. The ranks
# state an order, and §2's arrows state the order; an import the order
# allows but no docs row names is headroom, and the docs win on a
# conflict. A file directly
# under the group directory is the group root (today the Crypto facade
# and the Cli root); it may import every leaf of its group. base has
# no order in the docs, so
# the rule skips it. The §3.1 carve-out:
# within libp2p, negotiate and host import core and no implementation,
# so an import of security or mux from a negotiate or host file is a
# violation even though the ranks alone would allow it. Rule 3 runs
# inside rule 1's scan: one grep pass covers both import rules.
#
# Output: every violation goes to stderr as file:line, then exit 1.
# A clean tree gets one summary line on stdout.
set -euo pipefail

# Run from the repo root, wherever the caller stands.
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$root"

violations=0
checked=0

# A missing directory means a broken checkout. The checks cover
# `packages/` and all six group directories, so both scan loops read a
# whole tree. Fail loud with one clear line; a silent pass would hide
# the breakage.
for d in packages packages/base packages/codec packages/crypto packages/net packages/libp2p packages/cli; do
  if [ ! -d "$d" ]; then
    echo "lint-imports: $d is missing; the checkout is broken" >&2
    exit 1
  fi
done

# The rank of a leaf inside its group: the rule 3 table. Empty when
# the pair is unknown to it. The Crypto facade has no directory of its
# own; as an imported module it ranks above the leaves of crypto.
leafrank() {
  lrank=
  case $1 in
    net/streams)        lrank=1 ;;
    net/yamux)          lrank=2 ;;
    codec/varint)       lrank=1 ;;
    codec/snappy)       lrank=1 ;;
    codec/proto)        lrank=2 ;;
    codec/multiformats) lrank=2 ;;
    crypto/pure)        lrank=1 ;;
    crypto/backend)     lrank=1 ;;
    crypto/facade)      lrank=3 ;;
    libp2p/identity)    lrank=1 ;;
    libp2p/core)        lrank=2 ;;
    libp2p/security)    lrank=3 ;;
    libp2p/mux)         lrank=3 ;;
    libp2p/negotiate)   lrank=4 ;;
    libp2p/host)        lrank=5 ;;
    libp2p/protocols)   lrank=6 ;;
  esac
}

# Rule 1: every .lean file under a group directory joins the chain.
while IFS= read -r -d '' f; do
  group=${f#packages/}
  group=${group%%/*}
  case $group in
    cli)    rank=0 ;;
    libp2p) rank=1 ;;
    net)    rank=2 ;;
    crypto) rank=3 ;;
    codec)  rank=4 ;;
    base)   rank=5 ;;
    *) continue ;;  # outside the six groups: the chain does not govern it
  esac
  checked=$((checked + 1))

  # The importer leaf comes from the path: the first segment under the
  # group directory. A file directly under the group directory has no
  # leaf; it is the group root, and rule 3 does not restrict it.
  ileaf=
  sub=${f#packages/$group/}
  case $sub in */*) ileaf=${sub%%/*} ;; esac

  # The importer's rank decides what rule 3 allows. A leaf of a ranked
  # group that the table does not know is a broken table: fail loud,
  # a silent skip would hide it. base and cli have no order in the
  # docs, so their leaves stay outside the rule.
  irank=
  if [ -n "$ileaf" ]; then
    case $group in
      net|codec|crypto|libp2p)
        leafrank "$group/$ileaf"
        irank=$lrank
        if [ -z "$irank" ]; then
          echo "lint-imports: $f: leaf $ileaf has no rank in $group; extend the leafrank table" >&2
          exit 1
        fi ;;
    esac
  fi

  # The scan covers the whole file. Lean rejects imports placed later
  # (CLAUDE.md records the rule), and top-level indentation is legal,
  # which the widened pattern catches. `public import` parses on this
  # pin but cannot compile (`module` support is missing); it escapes
  # this pattern when a toolchain makes it compile. Revisit on a bump.
  # `|| true` keeps grep's no-match exit code out of set -e's way.
  imports=$(grep -nE '^[[:space:]]*import[[:space:]]+[A-Za-z_]' -- "$f" || true)
  while IFS= read -r line; do
    [ -n "$line" ] || continue
    lineno=${line%%:*}
    rest=${line#*:}
    read -r _ mod _ <<< "$rest"
    mod=${mod%$'\r'}  # CRLF files compile, and the carriage return would hide the module's group
    case $mod in
      Libp2p*) gname=libp2p; grank=1 ;;
      *)
        seg=${mod%%.*}
        case $seg in
          Cli)    gname=cli;    grank=0 ;;
          Streams|Yamux) gname=net;    grank=2 ;;
          Crypto|CryptoPure|Backend) gname=crypto; grank=3 ;;
          Varint|Multiformats|Proto|Snappy) gname=codec; grank=4 ;;
          Conc|Bytes) gname=base;   grank=5 ;;
          *) continue ;;  # external name, ignored
        esac
        ;;
    esac
    # The same group is allowed. Everything at or left of the importer
    # rank is a violation.
    if [ "$grank" -le "$rank" ] && [ "$gname" != "$group" ]; then
      echo "$f:$lineno: $group imports $mod ($gname); the chain allows only groups to the right" >&2
      violations=$((violations + 1))
    fi

    # Rule 3, checked here inside rule 1's scan: one grep pass covers
    # both import rules. The imported leaf comes from the module name:
    # the first segment decides, except libp2p where the second
    # segment decides (CLAUDE.md's Namespacing fixes the module form
    # `Libp2p.<Leaf>`; §2 names the leaves as directories). A module
    # the mapping does not know has no rank, so it stays outside the
    # rule.
    if [ "$gname" = "$group" ] && [ -n "$ileaf" ]; then
      mleaf=
      case $mod in
        Libp2p.*)
          sec=${mod#Libp2p.}
          sec=${sec%%.*}
          case $sec in
            Identity)  mleaf=identity  ;;
            Core)      mleaf=core      ;;
            Security)  mleaf=security  ;;
            Mux)       mleaf=mux       ;;
            Negotiate) mleaf=negotiate ;;
            Host)      mleaf=host      ;;
            Protocols) mleaf=protocols ;;
          esac ;;
        Libp2p*)
          # A dotless `Libp2p...` name has no second segment, so it
          # has no leaf; it stays outside the rule.
          ;;
        *)
          case $seg in
            Streams)      mleaf=streams      ;;
            Yamux)        mleaf=yamux        ;;
            Varint)       mleaf=varint       ;;
            Proto)        mleaf=proto        ;;
            Multiformats) mleaf=multiformats ;;
            Snappy)       mleaf=snappy       ;;
            CryptoPure)   mleaf=pure         ;;
            Backend)      mleaf=backend      ;;
            Crypto)       mleaf=facade       ;;
          esac ;;
      esac
      if [ -n "$mleaf" ]; then
        leafrank "$group/$mleaf"
        if [ -z "$lrank" ]; then
          echo "lint-imports: $f:$lineno: leaf $mleaf has no rank in $group; extend the leafrank table" >&2
          exit 1
        fi
        # The carve-out decides before the ranks: §3.1 forbids the
        # implementations under negotiate and host even where a rank
        # would allow the import.
        case "$ileaf/$mleaf" in
          negotiate/security|negotiate/mux|host/security|host/mux)
            echo "$f:$lineno: $ileaf imports $mod; negotiate and host import core and no implementation (§3.1)" >&2
            violations=$((violations + 1))
            ;;
          *)
            # Self is always allowed. Everything at or above the
            # importer's rank is a violation, equal ranks included
            # (siblings have no edge).
            if [ "$mleaf" != "$ileaf" ] && [ "$lrank" -ge "$irank" ]; then
              echo "$f:$lineno: $ileaf imports $mod ($mleaf); within $group the imports run downward only" >&2
              violations=$((violations + 1))
            fi
            ;;
        esac
      fi
    fi
  done <<< "$imports"
done < <(find packages -type f -name '*.lean' -print0 | sort -z)

# Rule 2: the four groups below libp2p never name it.
while IFS= read -r -d '' f; do
  matches=$(grep -in 'libp2p' -- "$f" || true)
  while IFS= read -r line; do
    [ -n "$line" ] || continue
    lineno=${line%%:*}
    group=${f#packages/}
    group=${group%%/*}
    echo "$f:$lineno: $group mentions libp2p; the packages below libp2p must not name it" >&2
    violations=$((violations + 1))
  done <<< "$matches"
done < <(find packages/base packages/codec packages/crypto packages/net -type f -name '*.lean' -print0 | sort -z)

if [ "$violations" -gt 0 ]; then
  exit 1
fi
echo "lint-imports: checked $checked module files, 0 violations"
