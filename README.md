# Overview
`ModNum` and `ModNumC` are highly ergonomic modular arithmetic structs intended 
for no_std use.

`ModNum` objects represent a value modulo m. The value and modulo can be of any
primitive integer type.  Arithmetic operators include +, - (both unary and binary),
*, /, `pow()`, and ==. Additional capabilities include computing multiplicative inverses
and solving modular equations. 

`ModNumC` objects likewise represent a value modulo M, where M is a generic constant of the
`usize` type. Arithmetic operators include +, - (both unary and binary), *, and ==.

This library was originally developed to facilitate bidirectional navigation through fixed-size
arrays at arbitrary starting points. This is facilitated by a double-ended iterator that
traverses the entire ring starting at any desired value. The iterator supports both `ModNum` and
`ModNumC.`

Note that `ModNum` and `ModNumC` are not designed to work with arbitrary-length integers, as
they require their integer type to implement the `Copy` trait.

# Updates
* **0.7**:
  * Added `ModNumC`, which uses [const generics](https://rust-lang.github.io/rfcs/2000-const-generics.html)
    to enable compile-time checking of compatible modulo. Its functionality is a proper
    subset of `ModNum`.
* **0.6**:
  * Learned that [`num::Saturating`](https://docs.rs/num/0.3.1/num/trait.Saturating.html) is deprecated.
  * Removed [`num::Saturating`](https://docs.rs/num/0.3.1/num/trait.Saturating.html) implementation.
  * Replaced by implementing [`num::traits::SaturatingAdd`](https://docs.rs/num/0.3.1/x86_64-pc-windows-msvc/num/traits/trait.SaturatingAdd.html) 
    and [`num::traits::SaturatingSub`](https://docs.rs/num/0.3.1/x86_64-pc-windows-msvc/num/traits/trait.SaturatingSub.html) instead.
* **0.5**:
  * Implemented the [`num::Saturating`](https://docs.rs/num/0.3.1/num/trait.Saturating.html) trait.
* **0.4**:
  * Added `ModNum` as a right-hand side option for arithmetic operators.
  * Implemented `Display` for `ModNum` objects.
* **0.3**: Added division and modular exponentiation with negative exponents.
* **0.2**: Added modular exponentiation and inverse.
    