import Multiformats.Radix

/-!
# The two base58 alphabets

Only the alphabet changes between the Bitcoin and Flickr forms. The
shared integer-base conversion preserves every leading zero byte.
-/

set_option autoImplicit false

namespace Multiformats.Base58

/-- The Bitcoin form omits characters that are easy to confuse. -/
def bitcoinAlphabet : String := "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"

/-- Flickr moves the lowercase letters before the uppercase letters. -/
def flickrAlphabet : String := "123456789abcdefghijkmnopqrstuvwxyzABCDEFGHJKLMNPQRSTUVWXYZ"

/-- The default form uses the Bitcoin alphabet. -/
def encode (bytes : ByteArray) : String := Radix.encode bitcoinAlphabet bytes

/-- Case matters in the Bitcoin alphabet. -/
def decode? (text : String) : Except Error ByteArray := Radix.decode? bitcoinAlphabet false text

/-- The second registered form shares all arithmetic with the default form. -/
def encodeFlickr (bytes : ByteArray) : String := Radix.encode flickrAlphabet bytes

/-- Case also matters in the Flickr alphabet. -/
def decodeFlickr? (text : String) : Except Error ByteArray := Radix.decode? flickrAlphabet false text

end Multiformats.Base58
