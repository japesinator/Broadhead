Broadhead
=========

An arrow-based parser combinator library for idris.

The actual combinators are pretty standard (`many`, `sepBy1`), but arrows are used instead of monads to combine parsers.  This should make it really fast at some future point, but at the moment it is not.  I would not recommend using this for anything ever in its current state.  Pull requests/issues/general contribution welcome.
