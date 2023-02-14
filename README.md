# Bare Metal Modulo

`ModNum` and `ModNumC` are highly ergonomic modular arithmetic structs intended 
for `no_std` use.

`ModNum` objects represent a value modulo m. The value and modulo can be of any
primitive integer type.  Arithmetic operators include `+`, `-` (both unary and binary),
`*`, `/`, `pow()`, and `==`. Additional capabilities include computing multiplicative inverses
and solving modular equations. 

`ModNumC` objects likewise represent a value modulo `M`, where `M` is a generic constant of the
`usize` type. Arithmetic operators include `+`, `-` (both unary and binary), `*`, and `==`.

This library was originally developed to facilitate bidirectional navigation through fixed-size
arrays at arbitrary starting points. This is facilitated by a double-ended iterator that
traverses the entire ring starting at any desired value. The iterator supports both `ModNum` and
`ModNumC.`

Modular numbers represent the remainder of an integer when divided by the modulo. If we also
store the quotient in addition to the remainder, we have a count of the number of times a
value had to "wrap around" during the calculation.

For example, if we start with **8 (mod 17)** and add **42**, the result is **16 (mod 17)** with
a wraparound of **2**. `WrapCountNum` and `WrapCountNumC` objects store this wraparound value 
and make it available. 

Furthermore, it is sometimes useful to be able to move back and forth in a range that is offset from zero. To that end, `OffsetNum` and `OffsetNumC` are provided.

Note that `ModNum`, `ModNumC`, `WrapCountNum`, `WrapCountNumC`, `OffsetNum`, and `OffsetNumC` are not designed to work with 
arbitrary-length integers, as they require their integer type to implement the `Copy` trait.

# Notes
* See [CHANGELOG.md](https://github.com/gjf2a/bare_metal_modulo/blob/master/CHANGELOG.md) for updates.
