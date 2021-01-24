# Overview
ModNum is a highly ergonomic modular arithmetic struct intended for no_std use.

ModNum objects represent a value modulo m. The value and modulo can be of any
primitive integer type.  Arithmetic operators include +, - (both unary and binary),
*, pow(), and ==. Additional capabilities include computing multiplicative inverses 
and solving modular equations.

ModNum was originally developed to facilitate bidirectional navigation through fixed-size
arrays at arbitrary starting points. This is facilitated by a double-ended iterator that
traverses the entire ring starting at any desired value.

Note that ModNum is not designed to work with arbitrary-length integers, as it requires its
integer type to implement the Copy trait.

# Updates
* **0.2**: Added modular exponentiation and inverse.
* **0.3**: Added division and modular exponentiation with negative exponents.
* **0.4**: 
  * Added `ModNum` as a right-hand side option for arithmetic operators.
  * Implemented `Display` for `ModNum` objects.
* **0.5**:
  * Implemented the [`num::Saturating`](https://docs.rs/num/0.3.1/num/trait.Saturating.html) trait.