ModNum is a highly ergonomic modular arithmetic struct intended for no_std use.

ModNum objects represent a value modulo m. The value and modulo can be of any
primitive integer type.  Arithmetic operators include +, - (both unary and binary),
*, and ==.

ModNum was originally developed to facilitate bidirectional navigation through fixed-size
arrays at arbitrary starting points. This is facilitated by a double-ended iterator that
traverses the entire ring starting at any desired value.

Note that ModNum is not designed to work with arbitrary-length integers, as it requires its
integer type to implement the Copy trait.

* [Documentation] (https://docs.rs/bare_metal_modulo/0.1.1/bare_metal_modulo/)
* [crates.io] (https://crates.io/crates/bare_metal_modulo)