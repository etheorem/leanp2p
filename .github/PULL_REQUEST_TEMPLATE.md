## Summary

<!-- One to three sentences. What does this PR change, and why?
     Link the issues it addresses. -->

## What changed

<!-- A bulleted list of the concrete code and doc changes. Group them
     by package if the PR spans more than one. -->

- 
- 

## Test plan

<!-- How did you verify the change? Check what applies. -->

- [ ] `lake build` (every package, on the pinned toolchain) is green.
- [ ] `lake test` passes, and passes again under `+RTS -N1`.
- [ ] The import-rule lint is green (ARCHITECTURE.md §2).
- [ ] A new codec or framing layer comes with its round-trip theorem or
      property test, and with a test for its length cap.
- [ ] If this touches wire behavior: the captured vectors still pass,
      and the description names the spec section the change follows.
- [ ] If this touches the go interop path: the interop matrix
      (PLAN W5.9) is green.

## Risk / trust footprint

<!-- Does this PR add or remove any axiom, `sorry`, `partial def`,
     `native_decide` invocation, `unsafe` block, or `@[extern]`
     declaration? List them. If none, write "none". -->

## Notes for reviewers

<!-- Anything that helps the reviewer get oriented: the design
     trade-offs you considered, the decisions you made under
     ambiguity, the follow-ups you deferred. -->

## LICENSE (LGPL version 3)
 - [x] I have read and accepted LICENSE (LGPL version 3), NOTICE and CLA in the root of this project.
