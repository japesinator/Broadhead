> module Broadhead.Example

> import Broadhead.Core
> import Broadhead.Combinator
> import Broadhead.Strings

We'll parse a simple sentence

> parseString (sepBy1 word spaces) "The quick brown fox jumped over the lazy dog"

This returns:

Right ["The",
      "quick",
      "brown",
      "fox",
      "jumped",
      "over",
      "the",
      "lazy",
      "dog"] : Either (List String) (List String)

The `Right` signifies that the parsing was successful, and then the result is a
`List` of `String`s, one for each word.  Had it failed, it would have returned a
`Left` with a `List` of error messages.
