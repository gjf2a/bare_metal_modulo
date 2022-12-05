#![cfg_attr(not(test), no_std)]
//! # Overview
//! The bare_metal_modulo crate includes the following structs:
//! - `ModNum` is a highly ergonomic modular arithmetic struct intended for `no_std` use.
//! - `ModNumC` is similar to `ModNum`, but uses
//!   [const generics](https://rust-lang.github.io/rfcs/2000-const-generics.html) to specify the
//!   modulo.
//! - `ModNumIterator` is a double-ended iterator that starts with the `ModNum` or `ModNumC` upon
//!   which it is invoked, making a complete traversal of the elements in that object's ring.
//! - `WrapCountNum` is similar to `ModNum`, but additionally tracks the amount of "wraparound"
//!   that produced the modulo value. `WrapCountNumC` corresponds to `ModNumC`.
//!
//! `ModNum` objects represent a value modulo **m**. The value and modulo can be of any
//! primitive integer type.  Arithmetic operators include `+`, `-` (both unary and binary),
//! `*`, `/`, `pow()`, `==`, `<`, `>`, `<=`, `>=`, and `!=`. Additional capabilities include
//! computing multiplicative inverses and solving modular equations. Division, multiplicative
//! inverse, and solving modular equations are only defined for signed types.
//!
//! `ModNumC` objects likewise represent a value modulo **M**, where **M** is a generic constant of
//! the `usize` type. `ModNumC` objects support the same arithmetic operators as `ModNum` objects.
//!
//! Modular numbers represent the remainder of an integer when divided by the modulo. If we also
//! store the quotient in addition to the remainder, we have a count of the number of times a
//! value had to "wrap around" during the calculation.
//!
//! For example, if we start with **8 (mod 17)** and add **42**, the result is **16 (mod 17)** with
//! a wraparound of **2**.
//!
//! `WrapCountNum`/`WrapCountNumC` objects store this wraparound value and make it available. They
//! only support subtraction and iteration with `Signed` values such as `isize` and `i64`.
//!
//! This library was originally developed to facilitate bidirectional navigation through fixed-size
//! arrays at arbitrary starting points. This is facilitated by a double-ended iterator that
//! traverses the entire ring starting at any desired value. The iterator supports
//! `ModNum` and `ModNumC`. It also supports `WrapCountNum` and `WrapCountNumC` for signed values
//! only.
//!
//! Note that `ModNum`, `ModNumC`, `WrapCountNum`, and `WrapCountNumC` are not designed to work
//! with arbitrary-length integers, as they require their integer type to implement the `Copy`
//! trait.
//!
//! For the [2020 Advent of Code](https://adventofcode.com/2020)
//! ([Day 13](https://adventofcode.com/2020/day/13) part 2),
//! I extended `ModNum` to solve systems of modular equations, provided that each modular equation
//! is represented using signed integers. My implementation is based on this
//! [lucid](https://byorgey.wordpress.com/2020/02/15/competitive-programming-in-haskell-modular-arithmetic-part-1/)
//! [explanation](https://byorgey.wordpress.com/2020/03/03/competitive-programming-in-haskell-modular-arithmetic-part-2/)
//! by [Brent Yorgey](http://ozark.hendrix.edu/~yorgey/).
//!
//! # Accessing Values
//! Each `ModNum`/`ModNumC`/`WrapCountNum`/`WrapCountNumC` represents an integer **a (mod m)**. To
//! access these values, use the corresponding **a()** and **m()** methods. Note that **a()** will
//! always return a fully reduced value, regardless of how it was initialized.
//!
//! Each `WrapCountNum`/`WrapCountNumC` tracks accumulated wraparounds. Use the **.wraps()** method
//! to access this tracked count.
//!
//!```
//! use bare_metal_modulo::*;
//!
//! let m = ModNum::new(7, 10);
//! assert_eq!(m.a(), 7);
//! assert_eq!(m.m(), 10);
//!
//! let n = ModNum::new(23, 17);
//! assert_eq!(n.a(), 6);
//! assert_eq!(n.m(), 17);
//!
//! let p = ModNum::new(-4, 3);
//! assert_eq!(p.a(), 2);
//! assert_eq!(p.m(), 3);
//!
//! let f = format!("{}", p);
//! assert_eq!(f, "2 (mod 3)");
//!
//! // ModNumC variables indicate the modulo using a type annotation.
//! let q: ModNumC<i32, 17> = ModNumC::new(23);
//! assert_eq!(q, 6);
//!
//! // Create a new ModNum with the same modulo as an existing one.
//! let r = p.with(8);
//! assert_eq!(r.a(), 2);
//! assert_eq!(r.m(), 3);
//!
//! let s = q.with(35);
//! assert_eq!(s.a(), 1);
//! assert_eq!(s.m(), 17);
//!
//! // Replace the value of the ModNum with a new value while keeping the modulo.
//! let mut t = ModNum::new(3, 5);
//! t.replace(12);
//! assert_eq!(t.a(), 2);
//!
//! let mut v: ModNumC<usize,5> = ModNumC::new(3);
//! v.replace(12);
//! assert_eq!(v.a(), 2);
//! ```
//!
//! # Arithmetic
//! Addition, subtraction, and multiplication are all fully supported for both
//! signed and unsigned integer types. The right-hand side may either be an integer of the
//! corresponding type or another `ModNum`/`ModNumC` object.
//!
//! Unary negation and subtraction are supported for both signed and unsigned integers.
//!
//! ```
//! use bare_metal_modulo::*;
//!
//! let mut m = ModNum::new(2, 5);
//! m += 2;
//! assert_eq!(m, ModNum::new(4, 5));
//! m += 2;
//! assert_eq!(m, ModNum::new(1, 5));
//! m -= 3;
//! assert_eq!(m, ModNum::new(3, 5));
//! m *= 2;
//! assert_eq!(m, ModNum::new(1, 5));
//! m *= 2;
//! assert_eq!(m, ModNum::new(2, 5));
//! m *= 2;
//! assert_eq!(m, ModNum::new(4, 5));
//! m *= 2;
//! assert_eq!(m, ModNum::new(3, 5));
//! m = -m;
//! assert_eq!(m, ModNum::new(2, 5));
//!
//! assert_eq!(m + ModNum::new(4, 5), ModNum::new(1, 5));
//! m += ModNum::new(4, 5);
//! assert_eq!(m, ModNum::new(1, 5));
//!
//! assert_eq!(m - ModNum::new(4, 5), ModNum::new(2, 5));
//! m -= ModNum::new(4, 5);
//! assert_eq!(m, ModNum::new(2, 5));
//!
//! assert_eq!(m * ModNum::new(3, 5), ModNum::new(1, 5));
//! m *= ModNum::new(3, 5);
//! assert_eq!(m, ModNum::new(1, 5));
//!
//! let mut m: ModNumC<isize,5> = ModNumC::new(2);
//! m *= 3;
//! assert_eq!(m, ModNumC::new(1));
//!
//! m += 1;
//! assert_eq!(m, ModNumC::new(2));
//!
//! m += 3;
//! assert_eq!(m, ModNumC::new(0));
//! ```
//!
//! Saturating addition and subtraction are often useful relative to the modulus, so the
//! [`num::traits::SaturatingAdd`](https://docs.rs/num-traits/0.2.14/num_traits/ops/saturating/trait.SaturatingAdd.html)
//! and
//! [`num::traits::SaturatingSub`](https://docs.rs/num-traits/0.2.14/num_traits/ops/saturating/trait.SaturatingSub.html)
//! traits are implemented as well for `ModNum` and `ModNumC`.
//!
//! ```
//! use bare_metal_modulo::*;
//! use num::traits::SaturatingAdd;
//! use num::traits::SaturatingSub;
//!
//! let m = ModNum::new(2, 5);
//! assert_eq!(m.saturating_add(&ModNum::new(1, 5)), ModNum::new(3, 5));
//! assert_eq!(m.saturating_add(&ModNum::new(2, 5)), ModNum::new(4, 5));
//! assert_eq!(m.saturating_add(&ModNum::new(3, 5)), ModNum::new(4, 5));
//! assert_eq!(m.saturating_sub(&ModNum::new(1, 5)), ModNum::new(1, 5));
//! assert_eq!(m.saturating_sub(&ModNum::new(2, 5)), ModNum::new(0, 5));
//! assert_eq!(m.saturating_sub(&ModNum::new(3, 5)), ModNum::new(0, 5));
//!
//! let m: ModNumC<i32, 5> = ModNumC::new(2);
//! assert_eq!(m.saturating_add(&ModNumC::new(1)), ModNumC::new(3));
//! assert_eq!(m.saturating_add(&ModNumC::new(2)), ModNumC::new(4));
//! assert_eq!(m.saturating_add(&ModNumC::new(3)), ModNumC::new(4));
//! assert_eq!(m.saturating_sub(&ModNumC::new(1)), ModNumC::new(1));
//! assert_eq!(m.saturating_sub(&ModNumC::new(2)), ModNumC::new(0));
//! assert_eq!(m.saturating_sub(&ModNumC::new(3)), ModNumC::new(0));
//! ```
//!
//! Multiplicative inverse (using the **.inverse()** method) is supported for signed integers only.
//! As inverses are only defined when **a** and **m** are relatively prime, **.inverse()** will
//! return **None** when it is not possible to calculate.
//!
//! Division is defined in terms of the multiplicative inverse, so it is likewise only supported
//! for signed integers, and will return **None** when the quotient does not exist. Assigned
//! division (/=) will **panic** if the quotient does not exist.
//!
//! The **.pow()** method is fully supported for unsigned integer types. It also works for signed
//! integer types, but it will **panic** if given a negative exponent. If negative exponents are
//! possible, use **.pow_signed()**, which will return **None** if the result does not exist.
//!
//! ```
//! use bare_metal_modulo::*;
//! use num::traits::Pow;
//!
//! let m = ModNum::new(2, 5);
//! assert_eq!(m.pow(2), ModNum::new(4, 5));
//! assert_eq!(m.pow(3), ModNum::new(3, 5));
//! assert_eq!(m.pow(4), ModNum::new(1, 5));
//! assert_eq!(m.pow(5), ModNum::new(2, 5));
//! assert_eq!(m.pow(6), ModNum::new(4, 5));
//!
//! assert_eq!(m.pow(ModNum::new(4, 5)), ModNum::new(1, 5));
//!
//! // Note: Very different result from m.pow(6)!
//! assert_eq!(m.pow(ModNum::new(6, 5)), ModNum::new(2, 5));
//!
//! let i = m.inverse().unwrap();
//! assert_eq!(m * i.a(), 1);
//!
//! assert_eq!(m.pow_signed(-2).unwrap(), ModNum::new(4, 5));
//! assert_eq!(m.pow_signed(-3).unwrap(), ModNum::new(2, 5));
//! assert_eq!(m.pow_signed(-4).unwrap(), ModNum::new(1, 5));
//! assert_eq!(m.pow_signed(-5).unwrap(), ModNum::new(3, 5));
//! assert_eq!(m.pow_signed(-6).unwrap(), ModNum::new(4, 5));
//!
//! let m = ModNum::new(6, 11);
//! assert_eq!((m / 2).unwrap().a(), 3);
//! assert_eq!((m / 4).unwrap().a(), 7);
//! assert_eq!((m / 5).unwrap().a(), 10);
//! assert_eq!((m / 6).unwrap().a(), 1);
//! assert_eq!((m / 8).unwrap().a(), 9);
//! assert_eq!(m / 0, None);
//!
//! assert_eq!((m / ModNum::new(2, 11)).unwrap(), ModNum::new(3, 11));
//! assert_eq!((m / ModNum::new(4, 11)).unwrap(), ModNum::new(7, 11));
//!
//! let m: ModNumC<i32,5> = ModNumC::new(2);
//!
//! let i = m.inverse().unwrap();
//! assert_eq!(m * i.a(), 1);
//!
//! assert_eq!(m.pow(2), ModNumC::new(4));
//! assert_eq!(m.pow(3), ModNumC::new(3));
//! assert_eq!(m.pow_signed(-2).unwrap(), ModNumC::new(4));
//! assert_eq!(m.pow_signed(-3).unwrap(), ModNumC::new(2));
//!
//! let m: ModNumC<i32, 11> = ModNumC::new(6);
//! assert_eq!((m / 2).unwrap().a(), 3);
//! assert_eq!((m / 4).unwrap().a(), 7);
//! assert_eq!(m / 0, None);
//! ```
//!
//! The **==** operator can be used to compare two `ModNum`s, two `ModNumC`s or a `ModNum`/`ModNumC`
//! and an integer of the corresponding type. In both cases, it represents congruence rather than
//! strict equality.
//!
//! Inequalities are also defined over those same sets.
//!
//!```
//! use bare_metal_modulo::*;
//!
//! let m = ModNum::new(2, 5);
//! assert!(m == 2);
//! assert!(m == 7);
//! assert!(m == -3);
//! assert!(m != 3);
//!
//! assert_eq!(m, ModNum::new(2, 5));
//! assert_eq!(m, ModNum::new(7, 5));
//! assert_eq!(m, ModNum::new(-3, 5));
//!
//! assert!(m < 4);
//! assert!(m < 8);
//! assert!(m > 1);
//!
//! let n = ModNum::new(6, 5);
//! assert!(m > n);
//! assert!(n < 2);
//! assert!(n > 0);
//!
//! let m: ModNumC<i32,5> = ModNumC::new(2);
//! assert!(m == 2);
//! assert!(m == 7);
//! assert!(m == -3);
//! assert!(m != 3);
//!
//! assert!(m < 4);
//! assert!(m < 8);
//! assert!(m > 1);
//!
//! let n: ModNumC<i32,5> = ModNumC::new(6);
//! assert!(m > n);
//! assert!(n < 2);
//! assert!(n > 0);
//! ```
//!
//! # Iteration
//! I originally created `ModNum` to facilitate cyclic iteration through a fixed-size array from an
//! arbitrary starting point in a `no_std` environment. Its double-ended iterator facilitates
//! both forward and backward iteration.
//!
//! ```
//! use bare_metal_modulo::*;
//!
//! let forward: Vec<usize> = ModNum::new(2, 5).iter().map(|mn| mn.a()).collect();
//! assert_eq!(forward, vec![2, 3, 4, 0, 1]);
//!
//! let reverse: Vec<usize> = ModNum::new(2, 5).iter().rev().map(|mn| mn.a()).collect();
//! assert_eq!(reverse, vec![1, 0, 4, 3, 2]);
//!
//! let m: ModNumC<usize,5> = ModNumC::new(2);
//! let forward: Vec<usize> = m.iter().map(|mn| mn.a()).collect();
//! assert_eq!(forward, vec![2, 3, 4, 0, 1]);
//!
//! let m: ModNumC<usize,5> = ModNumC::new(2);
//! let reverse: Vec<usize> = m.iter().rev().map(|mn| mn.a()).collect();
//! assert_eq!(reverse, vec![1, 0, 4, 3, 2]);
//! ```
//!
//! # Counting Wraps
//!
//! Modular numbers represent the remainder of an integer when divided by the modulo. If we also
//! store the quotient in addition to the remainder, we have a count of the number of times a
//! value had to "wrap around" during the calculation.
//!
//! For example, if we start with **8 (mod 17)** and add **42**, the result is **16 (mod 17)** with
//! a wraparound of **2**.
//!
//! `WrapCountNum` objects store this wraparound value and make it available. It is tracked through
//! both `+=` and `*=` for all supported numeric types.
//!
//! ```
//! use bare_metal_modulo::*;
//!
//! let mut value = WrapCountNum::new(8, 17);
//! value += 42;
//! assert_eq!(value, 16);
//! assert_eq!(value.wraps(), 2);
//!
//! value += 18;
//! assert_eq!(value, 0);
//! assert_eq!(value.wraps(), 4);
//!
//! value += 11;
//! assert_eq!(value, 11);
//! assert_eq!(value.wraps(), 4);
//!
//! value *= 5;
//! assert_eq!(value, 4);
//! assert_eq!(value.wraps(), 7);
//! ```
//!
//! Because regular operations produce a new `WordCountNum` value every time, `value = value + x`
//! only tracks wraps for a single operation, unlike `value += x`.
//!
//! ```
//! use bare_metal_modulo::*;
//! use num::traits::Pow;
//!
//! let mut value = WrapCountNum::new(8, 17);
//! value = value + 42;
//! assert_eq!(value, 16);
//! assert_eq!(value.wraps(), 2);
//!
//! value = value + 18;
//! assert_eq!(value, 0);
//! assert_eq!(value.wraps(), 2);
//!
//! value = value + 11;
//! assert_eq!(value, 11);
//! assert_eq!(value.wraps(), 0);
//!
//! value = value * 5;
//! assert_eq!(value, 4);
//! assert_eq!(value.wraps(), 3);
//!
//! value = value.pow(3);
//! assert_eq!(value, 13);
//! assert_eq!(value.wraps(), 3);
//! ```
//!
//! The `.pow_assign()` method enables wrap tracking when exponentiating.
//!
//! ```
//! use bare_metal_modulo::*;
//!
//! let mut value = WrapCountNum::new(4, 17);
//! value.pow_assign(3);
//! assert_eq!(value, 13);
//! assert_eq!(value.wraps(), 3);
//!
//! value += 6;
//! assert_eq!(value, 2);
//! assert_eq!(value.wraps(), 4);
//!
//! value.pow_assign(5);
//! assert_eq!(value, 15);
//! assert_eq!(value.wraps(), 5);
//! ```
//!
//! Subtraction causes the wrap count to decrease. To simplify the implementation, `WrapCountNum`
//! only defines subtraction on `Signed` numerical types.
//!
//! ```
//! use bare_metal_modulo::*;
//!
//! let mut value = WrapCountNum::new(2, 5);
//! value -= 8;
//! assert_eq!(value, 4);
//! assert_eq!(value.wraps(), -2);
//!
//! value -= 3;
//! assert_eq!(value, 1);
//! assert_eq!(value.wraps(), -2);
//!
//! value -= 13;
//! assert_eq!(value, 3);
//! assert_eq!(value.wraps(), -5);
//!
//! value += 8;
//! assert_eq!(value, 1);
//! assert_eq!(value.wraps(), -3);
//! ```
//!
//! There is a `const generic` version as well, `WrapCountNumC`:
//! ```
//! use bare_metal_modulo::*;
//!
//! let mut value = WrapCountNumC::<isize,17>::new(8);
//! value += 42;
//! assert_eq!(value, 16);
//! assert_eq!(value.wraps(), 2);
//!
//! value += 18;
//! assert_eq!(value, 0);
//! assert_eq!(value.wraps(), 4);
//!
//! value += 11;
//! assert_eq!(value, 11);
//! assert_eq!(value.wraps(), 4);
//!
//! value *= 5;
//! assert_eq!(value, 4);
//! assert_eq!(value.wraps(), 7);
//! ```
//!
//! # Hash/BTree keys
//! `ModNum` and `ModNumC` objects implement the `Ord` and `Hash` traits, and therefore can
//! be included in `HashSet` and `BTreeSet` collections and serve
//! as keys for `HashMap` and `BTreeMap` dictionaries.
//!
//! ```
//! use bare_metal_modulo::*;
//! use std::collections::HashSet;
//!
//! let m1: ModNumC<usize, 3> = ModNumC::new(2);
//! let m2: ModNumC<usize, 3> = ModNumC::new(4);
//! let m3: ModNumC<usize, 3> = ModNumC::new(5);
//! assert_eq!(m1, m3);
//! assert_eq!(m1 + 2, m2);
//!
//! let mut set = HashSet::new();
//! set.insert(m1);
//! set.insert(m2);
//! assert_eq!(set.len(), 2);
//! for m in [m1, m2, m3].iter() {
//!     assert!(set.contains(m));
//! }
//! ```
//! 
//! # Modular ranges rooted elsewhere than zero
//! 
//! Occasionally of use is the ability to represent a modular range of values starting elsewhere than zero. To address
//! this situation, `OffsetNumC` is provided. It has three generic parameters:
//! * Underlying integer type
//! * Number of values in the range
//! * Starting offset for the range
//! 
//! ```
//! use bare_metal_modulo::*;
//! 
//! let mut off = OffsetNumC::<i16, 7, 5>::new(5);
//! assert_eq!(off.a(), 5);
//! for i in 0..7 {
//!     off += 1;
//!     assert_eq!(off.a(), 5 + i);
//! }
//! assert_eq!(off.a(), 5);
//! ```
//!
//! # Solving Modular Equations with the Chinese Remainder Theorem
//! For the [2020 Advent of Code](https://adventofcode.com/2020)
//! ([Day 13](https://adventofcode.com/2020/day/13) part 2),
//! I extended `ModNum` to solve systems of modular equations, provided that each modular equation
//! is represented using signed integers. My implementation is based on this
//! [lucid](https://byorgey.wordpress.com/2020/02/15/competitive-programming-in-haskell-modular-arithmetic-part-1/)
//! [explanation](https://byorgey.wordpress.com/2020/03/03/competitive-programming-in-haskell-modular-arithmetic-part-2/)
//! by [Brent Yorgey](http://ozark.hendrix.edu/~yorgey/).
//!
//! The solver works directly with an iterator containing the `ModNum` objects corresponding to the
//! modular equations to be solved, facilitating space-efficient solutions of a sequence coming
//! from a stream. The examples below show two variants of the same system. The first example uses
//! an iterator, and the second example retrieves the system from a `Vec`.
//!
//! Note that the solution value can rapidly become large, as shown in the third example. I
//! recommend using **i128**, so as to maximize the set of solvable equations given this crate's
//! constraint of using **Copy** integers only. While the solution to the third example is
//! representable as an **i64**, some of the intermediate multiplications will overflow unless
//! **i128** is used.
//!
//! ```
//! use bare_metal_modulo::*;
//!
//! let mut values = (2..).zip((5..).step_by(2)).map(|(a, m)| ModNum::new(a, m)).take(3);
//! let solution = ModNum::<i128>::chinese_remainder_system(values);
//! assert_eq!(solution.unwrap().a(), 157);
//!
//! let values = vec![ModNum::new(2, 5), ModNum::new(3, 7), ModNum::new(4, 9)];
//! let solution = ModNum::<i128>::chinese_remainder_system(values.iter().copied());
//! assert_eq!(solution.unwrap().a(), 157);
//!
//!let mut values = [(0, 23), (28, 41), (20, 37), (398, 421), (11, 17), (15, 19), (6, 29),
//!    (433, 487), (11, 13), (5, 137), (19, 49)]
//!    .iter().copied().map(|(a, m)| ModNum::new(a, m));
//! let solution = ModNum::<i128>::chinese_remainder_system(values);
//! assert_eq!(solution.unwrap().a(), 762009420388013796);
//! ```

use core::cmp::Ordering;
use core::mem;
use num::{Integer, Signed, NumCast, FromPrimitive, Zero, One};
use core::ops::{Add, AddAssign, Sub, SubAssign, Mul, MulAssign, Neg, Div, DivAssign};
use num::traits::{Pow, SaturatingAdd, SaturatingSub};
use core::fmt::{Debug, Display, Formatter};

use trait_set::trait_set;
trait_set! {
    pub trait NumType = Copy + Clone + Integer + Display + Debug + NumCast + FromPrimitive + AddAssign + SubAssign + MulAssign + DivAssign;
}

pub trait MNum : Copy + Eq + PartialEq {
    type Num: NumType;

    fn a(&self) -> Self::Num;

    fn m(&self) -> Self::Num;

    fn with(&self, new_a: Self::Num) -> Self;

    fn replace(&mut self, new_a: Self::Num) {
        *self = self.with(new_a);
    }

    /// [Extended Euclidean Algorithm for Greatest Common Divisor](https://byorgey.wordpress.com/2020/02/15/competitive-programming-in-haskell-modular-arithmetic-part-1/) for GCD.
    ///
    /// This is my translation into Rust of [Brent Yorgey's Haskell implementation](https://byorgey.wordpress.com/2020/02/15/competitive-programming-in-haskell-modular-arithmetic-part-1/).
    ///
    /// Given two integers **a** and **b**, it returns three integer values:
    /// - Greatest Common Divisor (**g**) of **a** and **b**
    /// - Two additional values **x** and **y**, where **ax + by = g**
    fn egcd(a: Self::Num, b: Self::Num) -> (Self::Num,Self::Num,Self::Num) where Self::Num: Signed {
        if b == Self::Num::zero() {
            (a.signum() * a, a.signum(), Self::Num::zero())
        } else {
            let (g, x, y) = Self::egcd(b, a.mod_floor(&b));
            (g, y, x - (a / b) * y)
        }
    }

    /// Returns the modular inverse, if it exists. Returns **None** if it does not exist.
    ///
    /// This is my translation into Rust of [Brent Yorgey's Haskell implementation](https://byorgey.wordpress.com/2020/02/15/competitive-programming-in-haskell-modular-arithmetic-part-1/).
    ///
    /// Let **m = ModNum::new(a, m)**, where **a** and **m** are relatively prime.
    /// Then **m * m.inverse().unwrap().a()** is congruent to **1 (mod m)**.
    ///
    /// Returns None if **a** and **m** are not relatively prime.
    fn inverse(&self) -> Option<Self> where Self::Num: Signed {
        let (g, _, inv) = Self::egcd(self.m(), self.a());
        if g == Self::Num::one() {Some(self.with(inv))} else {None}
    }
}

/// Represents an integer **a (mod m)**
#[derive(Debug,Copy,Clone,Eq,PartialEq,Ord,PartialOrd,Hash)]
pub struct ModNum<N> {
    num: N,
    modulo: N
}

impl <N:NumType> MNum for ModNum<N> {
    type Num = N;

    fn a(&self) -> N {
        self.num
    }

    fn m(&self) -> N {
        self.modulo
    }

    fn with(&self, new_a: Self::Num) -> Self {
        Self::new(new_a, self.m())
    }
}

impl <N: NumType> ModNum<N> {
    /// Creates a new integer **a (mod m)**
    pub fn new(a: N, m: N) -> Self {
        ModNum { num: a.mod_floor(&m), modulo: m }
    }

    /// Returns an iterator starting at **a (mod m)** and ending at **a - 1 (mod m)**
    pub fn iter(&self) -> ModNumIterator<N,Self> {
        ModNumIterator::new(*self)
    }
}

impl <N: NumType + Signed> ModNum<N> {

    /// Solves a pair of modular equations using the [Chinese Remainder Theorem](https://byorgey.wordpress.com/2020/03/03/competitive-programming-in-haskell-modular-arithmetic-part-2/).
    ///
    /// This is my translation into Rust of [Brent Yorgey's Haskell implementation](https://byorgey.wordpress.com/2020/03/03/competitive-programming-in-haskell-modular-arithmetic-part-2/).
    ///
    /// - `self` represents the modular equation **x = a (mod m)**
    /// - `other` represents the modular equation **x = b (mod n)**
    /// - It returns a `ModNum` corresponding to the equation **x = c (mod mn)** where
    ///   **c** is congruent both to **a (mod m)** and **b (mod n)**
    pub fn chinese_remainder(&self, other: ModNum<N>) -> ModNum<N> {
        let (g, u, v) = ModNum::egcd(self.m(), other.m());
        let c = (self.a() * other.m() * v + other.a() * self.m() * u).div_floor(&g);
        ModNum::new(c, self.m() * other.m())
    }

    /// Solves a system of modular equations using `ModMum::chinese_remainder()`.
    ///
    /// Each equation in the system is an element of the **modnums** iterator parameter.
    /// - Returns **None** if the iterator is empty.
    /// - Returns **Some(element)** if the iterator has only one element.
    /// - Returns **Some(solution)** if the iterator has two or more elements, where the solution is
    ///   found by repeatedly calling **ModNum::chinese_remainder()**.
    pub fn chinese_remainder_system<I:Iterator<Item=ModNum<N>>>(mut modnums: I) -> Option<ModNum<N>> {
        modnums.next().map(|start_num|
            modnums.fold(start_num, |a, b| a.chinese_remainder(b)))
    }
}

macro_rules! derive_assign {
    ($name:ty, $implname:ty, $rhs_type:ty, $methodname:ident {$symbol:tt} {$($generic:tt)*} {$($num_type_suffix:ident)?} {$($unwrap:tt)*}) => {
        impl <N: NumType + $($num_type_suffix)?,$($generic)*> $implname for $name {
            fn $methodname(&mut self, rhs: $rhs_type) {
                *self = (*self $symbol rhs)$($unwrap)*;
            }
        }
    }
}

macro_rules! derive_core_modulo_arithmetic {
    ($name:ty {$($generic:tt)*}) => {

        /// Returns **true** if **other** is congruent to **self.a() (mod self.m())**
        impl <N:NumType,$($generic)*> PartialEq<N> for $name {
            fn eq(&self, other: &N) -> bool {
                self.num == other.mod_floor(&self.m())
            }
        }

        impl <N:NumType,$($generic)*> PartialOrd<N> for $name {
            fn partial_cmp(&self, other: &N) -> Option<Ordering> {
                self.a().partial_cmp(other)
            }
        }

        impl <N: NumType,$($generic)*> Add<N> for $name {
            type Output = Self;

            fn add(self, rhs: N) -> Self::Output {
                self.with(self.a() + rhs)
            }
        }

        impl <N: NumType,$($generic)*> Add<$name> for $name {
            type Output = Self;

            fn add(self, rhs: Self) -> Self::Output {
                self + rhs.a()
            }
        }

        impl <N: NumType,$($generic)*> Mul<N> for $name {
            type Output = Self;

            fn mul(self, rhs: N) -> Self::Output {
                self.with(self.a() * rhs)
            }
        }

        impl <N: NumType,$($generic)*> Mul<$name> for $name {
            type Output = Self;

            fn mul(self, rhs: Self) -> Self::Output {
                assert_eq!(self.m(), rhs.m());
                self * rhs.a()
            }
        }

        impl <N: NumType + Signed,$($generic)*> Div<N> for $name {
            type Output = Option<Self>;

            fn div(self, rhs: N) -> Self::Output {
                self.with(rhs).inverse().map(|inv| self * inv.a())
            }
        }

        impl <N: NumType + Signed,$($generic)*> Div<$name> for $name {
            type Output = Option<Self>;

            fn div(self, rhs: Self) -> Self::Output {
                self / rhs.a()
            }
        }

        impl <N: NumType,$($generic)*> Pow<N> for $name {
            type Output = Self;

            /// Returns a^rhs (mod m), for rhs >= 0.
            /// Implements efficient modular exponentiation by [repeated squaring](https://byorgey.wordpress.com/2020/02/15/competitive-programming-in-haskell-modular-arithmetic-part-1/).
            ///
            /// Panics if rhs < 0. If negative exponents are possible, use .pow_signed()
            fn pow(self, rhs: N) -> Self::Output {
                if rhs < N::zero() {
                    panic!("Negative exponentiation undefined for ModNum.pow(). Try .pow_signed() instead.")
                } else if rhs == N::zero() {
                    self.with(N::one())
                } else {
                    let mut r = self.pow(rhs.div_floor(&(N::one() + N::one())));
                    r *= r;
                    if rhs.is_odd() {
                        r *= self;
                    }
                    r
                }
            }
        }

        impl <N: NumType,$($generic)*> Pow<$name> for $name {
            type Output = Self;

            fn pow(self, rhs: Self) -> Self::Output {
                self.pow(rhs.a())
            }
        }

        /// Exponentiates safely with negative exponents - if the inverse is undefined, it returns
        /// `None`, otherwise it returns `Some(self.pow(rhs))`.
        impl <N: NumType + Signed,$($generic)*> $name {
            pub fn pow_signed(&self, rhs: N) -> Option<Self> {
                if rhs < N::zero() {
                    self.pow(-rhs).inverse()
                } else {
                    Some(self.pow(rhs))
                }
            }
        }
    }
}

macro_rules! derive_modulo_arithmetic {
    ($name:ty {$($generic:tt)*}) => {

        derive_core_modulo_arithmetic! {
            $name
            {$($generic)*}
        }

        impl <N:NumType,$($generic)*> Display for $name {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                write!(f, "{} (mod {})", self.a(), self.m())
            }
        }

        derive_assign! {
            $name, AddAssign<N>, N, add_assign {+} {$($generic)*} {} {}
        }

        derive_assign! {
            $name, AddAssign<$name>, $name, add_assign {+} {$($generic)*} {} {}
        }

        impl <N: NumType,$($generic)*> Neg for $name {
            type Output = Self;

            fn neg(self) -> Self::Output {
                self.with(self.m() - self.num)
            }
        }

        impl <N: NumType,$($generic)*> Sub<N> for $name {
            type Output = Self;

            fn sub(self, rhs: N) -> Self::Output {
                self + (-self.with(rhs)).a()
            }
        }

        impl <N: NumType,$($generic)*> Sub<$name> for $name {
            type Output = Self;

            fn sub(self, rhs: Self) -> Self::Output {
                self - rhs.a()
            }
        }

        derive_assign! {
            $name, SubAssign<N>, N, sub_assign {-} {$($generic)*} {} {}
        }

        derive_assign! {
            $name, SubAssign<$name>, $name, sub_assign {-} {$($generic)*} {} {}
        }

        derive_assign! {
            $name, MulAssign<N>, N, mul_assign {*} {$($generic)*} {} {}
        }

        derive_assign! {
            $name, MulAssign<$name>, $name, mul_assign {*} {$($generic)*} {} {}
        }

        derive_assign! {
            $name, DivAssign<N>, N, div_assign {/} {$($generic)*} {Signed} {.unwrap()}
        }

        derive_assign! {
            $name, DivAssign<$name>, $name, div_assign {/} {$($generic)*} {Signed} {.unwrap()}
        }

        impl <N: NumType, $($generic)*> SaturatingAdd for $name {
            fn saturating_add(&self, v: &Self) -> Self {
                if self.a() + v.a() >= self.m() {
                    self.with(self.m() - N::one())
                } else {
                    *self + *v
                }
            }
        }

        impl <N: NumType, $($generic)*> SaturatingSub for $name {
            fn saturating_sub(&self, v: &Self) -> Self {
                if self.a() < v.a() {
                    self.with(N::zero())
                } else {
                    *self - *v
                }
            }
        }
    }
}

derive_modulo_arithmetic! {
    ModNum<N> {}
}

/// A double-ended iterator that starts with the ModNum upon which it is invoked,
/// making a complete traversal of the elements in that ModNum's ring.
#[derive(Debug)]
pub struct ModNumIterator<N:NumType,M:MNum<Num=N> + Add<N,Output=M> + Sub<N,Output=M>> {
    next: M,
    next_back: M,
    finished: bool
}

impl <N: NumType,M:MNum<Num=N> + Add<N,Output=M> + Sub<N,Output=M>> ModNumIterator<N,M> {
    pub fn new(mn: M) -> Self {
        ModNumIterator {next: mn, next_back: mn - N::one(), finished: false}
    }
}

fn update<N: NumType, M:MNum<Num=N> + Add<N,Output=M> + Sub<N,Output=M>, F:Fn(&M,N)->M>(finished: &mut bool, update: &mut M, updater: F, target: M) -> Option<<ModNumIterator<N,M> as Iterator>::Item> {
    if *finished {
        None
    } else {
        let mut future = updater(update, N::one());
        if future == updater(&target, N::one()) {
            *finished = true;
        }
        mem::swap(&mut future, update);
        Some(future)
    }
}

impl <N: NumType, M:MNum<Num=N> + Add<N,Output=M> + Sub<N,Output=M>> Iterator for ModNumIterator<N,M> {
    type Item = M;

    fn next(&mut self) -> Option<Self::Item> {
        update(&mut self.finished, &mut self.next, |m, u| *m + u, self.next_back)
    }
}

impl <N: NumType, M:MNum<Num=N> + Add<N,Output=M> + Sub<N,Output=M>> DoubleEndedIterator for ModNumIterator<N,M> {
    fn next_back(&mut self) -> Option<Self::Item> {
        update(&mut self.finished, &mut self.next_back, |m, u| *m - u, self.next)
    }
}

/// Represents an integer **a (mod M)**
#[derive(Debug,Copy,Clone,Eq,PartialEq,Ord,PartialOrd,Hash)]
pub struct ModNumC<N: FromPrimitive, const M: usize> {
    num: N
}

impl <N:NumType, const M: usize> MNum for ModNumC<N,M> {
    type Num = N;

    fn a(&self) -> Self::Num {
        self.num
    }

    fn m(&self) -> Self::Num {
        N::from_usize(M).unwrap()
    }

    fn with(&self, new_a: Self::Num) -> Self {
        Self::new(new_a)
    }
}

impl <N: NumType, const M: usize> ModNumC<N,M> {
    pub fn new(num: N) -> Self {
        let mut result = ModNumC {num};
        result.num = result.num.mod_floor(&result.m());
        result
    }

    /// Returns an iterator starting at **a (mod m)** and ending at **a - 1 (mod m)**
    pub fn iter(&self) -> ModNumIterator<N,Self> {
        ModNumIterator::new(*self)
    }
}

derive_modulo_arithmetic! {
    ModNumC<N,M> {const M: usize}
}

/// Represents an integer **a (mod M)**
#[derive(Debug,Copy,Clone,Eq,PartialEq,Ord,PartialOrd,Hash)]
pub struct WrapCountNum<N: NumType> {
    num: N,
    modulo: N,
    wraps: N
}

impl <N: NumType> MNum for WrapCountNum<N> {
    type Num = N;

    fn a(&self) -> Self::Num {
        self.num
    }

    fn m(&self) -> Self::Num {
        self.modulo
    }

    fn with(&self, new_a: Self::Num) -> Self {
        Self::new(new_a, self.m())
    }
}

impl <N: NumType> WrapCountNum<N> {
    /// Creates a new integer **a (mod m)**, storing the number of wraparounds
    /// of **a** as well.
    pub fn new(a: N, modulo: N) -> Self {
        let (wraps, num) = a.div_mod_floor(&modulo);
        WrapCountNum { num, modulo, wraps }
    }

    pub fn with_wraps(&self, a: N, wraps: N) -> Self {
        WrapCountNum {num: a, modulo: self.modulo, wraps}
    }
}

macro_rules! derive_wrap_assign {
    ($name:ty, $implname:ty, $rhs_type:ty, $methodname:ident {$symbol:tt} {$($generic:tt)*} {$($num_type_suffix:ident)?} {$($unwrap:tt)*}) => {
        impl <N: NumType + $($num_type_suffix)?,$($generic)*> $implname for $name {
            fn $methodname(&mut self, rhs: $rhs_type) {
                let result = (*self $symbol rhs)$($unwrap)*;
                self.num = result.num;
                self.wraps += result.wraps;
            }
        }
    }
}

macro_rules! derive_wrap_modulo_arithmetic {
    ($name:ty {$($generic:tt)*}) => {
        derive_core_modulo_arithmetic! {$name {$($generic)*}}

        impl <N: NumType,$($generic)*> $name {
            /// Returns the total number of wraparounds counted when calculating this value.
            pub fn wraps(&self) -> N {
                self.wraps
            }

            pub fn pow_assign(&mut self, rhs: N) {
                let result = self.pow(rhs);
                self.num = result.num;
                self.wraps += result.wraps;
            }
        }

        impl <N: NumType + Signed,$($generic)*> $name {
            /// Returns an iterator starting at **a (mod m)** and ending at **a - 1 (mod m)**
            pub fn iter(&self) -> ModNumIterator<N,Self> {
                ModNumIterator::new(*self)
            }

            /// Computes and assigns to `self` the value `self.pow_signed(rhs)`. If the result
            /// is undefined due to `rhs` not having a defined inverse, `self` will be unchanged.
            pub fn pow_assign_signed(&mut self, rhs: N) {
                let result = self.pow_signed(rhs);
                if let Some(result) = result {
                    self.num = result.num;
                    self.wraps += result.wraps;
                }
            }
        }

        impl <N: NumType,$($generic)*> Display for $name {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                write!(f, "{} (mod {}) (wrap {})", self.a(), self.m(), self.wraps)
            }
        }

        impl <N: NumType + Signed,$($generic)*> Neg for $name {
            type Output = Self;

            fn neg(self) -> Self::Output {
                self.with_wraps(-self.num, -self.wraps)
            }
        }

        impl <N: NumType + Signed,$($generic)*> Sub<N> for $name {
            type Output = Self;

            fn sub(self, rhs: N) -> Self::Output {
                self.with(self.num - rhs)
            }
        }

        impl <N: NumType + Signed,$($generic)*> Sub<$name> for $name {
            type Output = Self;

            fn sub(self, rhs: $name) -> Self::Output {
                self - rhs.a()
            }
        }

        derive_wrap_assign! {
            $name, AddAssign<N>, N, add_assign {+} {$($generic)*} {} {}
        }

        derive_wrap_assign! {
            $name, AddAssign<$name>, $name, add_assign {+} {$($generic)*} {} {}
        }

        derive_wrap_assign! {
            $name, SubAssign<N>, N, sub_assign {-} {$($generic)*} {Signed} {}
        }

        derive_wrap_assign! {
            $name, SubAssign<$name>, $name, sub_assign {-} {$($generic)*} {Signed} {}
        }

        derive_wrap_assign! {
            $name, MulAssign<N>, N, mul_assign {*} {$($generic)*} {} {}
        }

        derive_wrap_assign! {
            $name, MulAssign<$name>, $name, mul_assign {*} {$($generic)*} {} {}
        }

        derive_wrap_assign! {
            $name, DivAssign<N>, N, div_assign {/} {$($generic)*} {Signed} {.unwrap()}
        }

        derive_wrap_assign! {
            $name, DivAssign<$name>, $name, div_assign {/} {$($generic)*} {Signed} {.unwrap()}
        }
    }
}

derive_wrap_modulo_arithmetic! {
    WrapCountNum<N> {}
}

#[derive(Debug,Copy,Clone,Eq,PartialEq,Ord,PartialOrd,Hash)]
pub struct WrapCountNumC<N: FromPrimitive, const M: usize> {
    num: N, wraps: N
}

impl <N:NumType, const M: usize> MNum for WrapCountNumC<N,M> {
    type Num = N;

    fn a(&self) -> Self::Num {
        self.num
    }

    fn m(&self) -> Self::Num {
        N::from_usize(M).unwrap()
    }

    fn with(&self, new_a: Self::Num) -> Self {
        Self::new(new_a)
    }
}

impl <N: NumType, const M: usize> WrapCountNumC<N,M> {
    /// Creates a new integer **a (mod m)**, storing the number of wraparounds
    /// of **a** as well.
    pub fn new(a: N) -> Self {
        let mut result = WrapCountNumC {num: a, wraps: N::zero()};
        let (wraps, num) = a.div_mod_floor(&result.m());
        result.num = num;
        result.wraps = wraps;
        result
    }

    pub fn with_wraps(&self, a: N, wraps: N) -> Self {
        WrapCountNumC {num: a, wraps}
    }
}

derive_wrap_modulo_arithmetic! {
    WrapCountNumC<N,M> {const M: usize}
}

#[derive(Debug,Copy,Clone,Eq,PartialEq,Ord,PartialOrd,Hash)]
pub struct OffSetNum<N: FromPrimitive> {
    num: N,
    modulo: N,
    offset: N,
}

fn offset_init<N: NumType>(num: N, modulo: N, offset: N) -> N {
    let mut num = num;
    while num < offset {
        num += modulo;
    }
    num - offset
}

/* 
impl <N:FromPrimitive> OffsetNum<N> {
    pub fn new(num: N, modulo: N, offset: N) {
        let num = (num - offset)
    }
}

impl <N:NumType> MNum for OffSetNum<N> {
    type Num = N;

    fn a(&self) -> N {
        self.num + self.offset
    }

    fn m(&self) -> N {
        self.modulo
    }

    fn with(&self, new_a: Self::Num) -> Self {
        Self::new(new_a, self.m())
    }
}
*/
#[derive(Debug,Copy,Clone,Eq,PartialEq,Ord,PartialOrd,Hash)]
pub struct OffsetNumC<N: FromPrimitive, const M: usize, const O: isize> {
    num: N
}

impl <N:NumType, const M: usize, const O: isize> MNum for OffsetNumC<N,M,O> {
    type Num = N;

    fn a(&self) -> Self::Num {
        self.num + N::from_isize(O).unwrap()
    }

    fn m(&self) -> Self::Num {
        N::from_usize(M).unwrap()
    }

    fn with(&self, new_a: Self::Num) -> Self {
        Self::new(new_a)
    }
}

impl <N:NumType, const M: usize, const O: isize> OffsetNumC<N,M,O> {
    pub fn new(num: N) -> Self {
        let num = offset_init(num, N::from_usize(M).unwrap(), N::from_isize(O).unwrap());
        let mut result = OffsetNumC {num};
        result.num = result.num.mod_floor(&result.m());
        result
    }
}

derive_modulo_arithmetic! {
    OffsetNumC<N,M,O> {const M: usize, const O: isize}
}

#[cfg(test)]
mod tests {
    extern crate alloc;
    use alloc::vec;
    use alloc::vec::Vec;
    use super::*;

    #[test]
    fn test_neg() {
        let m = ModNum::new(-2, 5);
        assert_eq!(m, ModNum::new(3, 5));
    }

    #[test]
    fn test_negation() {
        for n in 0..5 {
            let m = ModNum::new(n, 5);
            let n = -m;
            assert_eq!(m + n.a(), 0);
        }
    }

    #[test]
    fn test_sub() {
        for (n, m, sub, target) in vec![(1, 5, 2, 4)] {
            assert_eq!(ModNum::new(n, m) - sub, ModNum::new(target, m));
        }
    }

    #[test]
    fn test_neg_c() {
        let m: ModNumC<i32,5> = ModNumC::new(-2);
        assert_eq!(m, ModNumC::new(3));
    }

    #[test]
    fn test_negation_c() {
        let s: ModNumC<i32,5> = ModNumC::new(0);
        for m in s.iter() {
            let n = -m;
            assert_eq!(m + n, 0);
        }
    }

    #[test]
    fn test_sub_c() {
        for (n, sub, target) in vec![(1, 2, 4), (2, 1, 1), (4, 1, 3), (4, 4, 0), (2, 5, 2)] {
            let n: ModNumC<i32,5> = ModNumC::new(n);
            assert_eq!(n - sub, target);
        }
    }

    #[test]
    fn test_congruence_c() {
        let m: ModNumC<i32,5> = ModNumC::new(2);
        for c in (-13..13).step_by(5) {
            assert_eq!(m, c);
            for i in -2..=2 {
                if i == 0 {
                    assert_eq!(m, c);
                } else {
                    assert_ne!(m, c + i);
                }
            }
        }
    }

    #[test]
    fn test_iter_up() {
        assert_eq!(vec![2, 3, 4, 0, 1], ModNum::new(2, 5).iter().map(|m: ModNum<usize>| m.a()).collect::<Vec<usize>>())
    }

    #[test]
    fn test_iter_down() {
        assert_eq!(vec![1, 0, 4, 3, 2], ModNum::new(2, 5).iter().rev().map(|m: ModNum<usize>| m.a()).collect::<Vec<usize>>())
    }

    #[test]
    fn test_iter_up_w() {
        assert_eq!(vec![2, 3, 4, 0, 1], WrapCountNumC::<isize,5>::new(2).iter().map(|m: WrapCountNumC<isize,5>| m.a()).collect::<Vec<isize>>())
    }

    #[test]
    fn test_iter_down_w() {
        assert_eq!(vec![1, 0, 4, 3, 2], WrapCountNumC::<isize,5>::new(2).iter().rev().map(|m: WrapCountNumC<isize,5>| m.a()).collect::<Vec<isize>>())
    }

    #[test]
    fn test_inverse() {
        for a in 0..13 {
            let m = ModNum::new(a, 13);
            let inv = m.inverse();
            if a == 0 {
                assert!(inv.is_none());
            } else {
                assert_eq!(m * inv.unwrap().a(), 1);
            }
        }
    }

    #[test]
    fn test_assign() {
        let mut m = ModNum::new(2, 5);
        m += 2;
        assert_eq!(m, ModNum::new(4, 5));
        m += 2;
        assert_eq!(m, ModNum::new(1, 5));
        m -= 3;
        assert_eq!(m, ModNum::new(3, 5));
        m *= 2;
        assert_eq!(m, ModNum::new(1, 5));
        m *= 2;
        assert_eq!(m, ModNum::new(2, 5));
        m *= 2;
        assert_eq!(m, ModNum::new(4, 5));
        m *= 2;
        assert_eq!(m, ModNum::new(3, 5));
    }

    #[test]
    fn test_assign_2() {
        let mut m = ModNum::new(2, 5);
        m += ModNum::new(2, 5);
        assert_eq!(m, ModNum::new(4, 5));
        m += ModNum::new(2, 5);
        assert_eq!(m, ModNum::new(1, 5));
        m -= ModNum::new(3, 5);
        assert_eq!(m, ModNum::new(3, 5));
        m *= ModNum::new(2, 5);
        assert_eq!(m, ModNum::new(1, 5));
        m *= ModNum::new(2, 5);
        assert_eq!(m, ModNum::new(2, 5));
        m *= ModNum::new(2, 5);
        assert_eq!(m, ModNum::new(4, 5));
        m *= ModNum::new(2, 5);
        assert_eq!(m, ModNum::new(3, 5));
    }

    #[test]
    fn test_chinese_remainder() {
        let x = ModNum::new(2, 5);
        let y = ModNum::new(3, 7);
        assert_eq!(x.chinese_remainder(y), ModNum::new(17, 35));
    }

    #[test]
    fn test_chinese_systems() {
        // Examples from 2020 Advent of Code, Day 13 Puzzle 2.
        let systems = vec![
            (vec![(2, 5), (3, 7), (4, 9)], 157),
            (vec![(0, 17), (-2, 13), (-3, 19)], 3417),
            (vec![(0, 67), (-1, 7), (-2, 59), (-3, 61)], 754018),
            (vec![(0, 67), (-2, 7), (-3, 59), (-4, 61)], 779210),
            (vec![(0, 67), (-1, 7), (-3, 59), (-4, 61)], 1261476),
            (vec![(0, 1789), (-1, 37), (-2, 47), (-3, 1889)], 1202161486)
        ];
        for (system, goal) in systems {
            let mut equations = system.iter().copied()
                .map(|(a, m)| ModNum::<i128>::new(a, m));
            assert_eq!(ModNum::chinese_remainder_system(&mut equations).unwrap().a(), goal);
        }
    }

    #[test]
    fn test_congruence() {
        let m = ModNum::new(2, 5);
        for c in (-13..13).step_by(5) {
            assert_eq!(m, c);
            for i in -2..=2 {
                if i == 0 {
                    assert_eq!(m, c);
                } else {
                    assert_ne!(m, c + i);
                }
            }
        }
    }

    #[test]
    fn test_division() {
        let m = ModNum::new(6, 11);
        for undefined in [0, 11].iter() {
            assert_eq!(m / *undefined, None);
        }
        for (divisor, quotient) in [(1, 6), (2, 3), (4, 7), (5, 10), (8, 9)].iter() {
            for (d, q) in [(divisor, quotient), (quotient, divisor)].iter() {
                let result = (m / **d).unwrap();
                assert_eq!(result * **d, m);
                assert_eq!(result.a(), **q);
            }
        }
    }

    #[test]
    fn test_pow() {
        let m = ModNum::new(2, 5);
        for (exp, result) in (2..).zip([4, 3, 1, 2].iter().cycle()).take(20) {
            assert_eq!(m.pow(exp).a(), *result);
        }
    }

    #[test]
    fn test_big() {
        let mut values = [(0, 23), (28, 41), (20, 37), (398, 421), (11, 17), (15, 19), (6, 29),
            (433, 487), (11, 13), (5, 137), (19, 49)]
            .iter().copied().map(|(a, m)| ModNum::new(a, m));
        let solution = ModNum::<i128>::chinese_remainder_system(&mut values).unwrap().a();
        assert_eq!(solution, 762009420388013796);
    }

    #[test]
    fn test_negative_exp() {
        let m = ModNum::new(2, 5);
        for (exp, result) in (2..).map(|n| -n).zip([4, 2, 1, 3].iter().cycle()).take(20) {
            assert_eq!(m.pow_signed(exp).unwrap().a(), *result);
        }
    }

    #[test]
    fn test_wrapping() {
        let mut w: WrapCountNumC<usize, 5> = WrapCountNumC::new(4);
        w *= 4;
        assert_eq!(w, 1);
        assert_eq!(w.wraps(), 3);
        w += 9;
        assert_eq!(w, 0);
        assert_eq!(w.wraps(), 5);
    }

    #[test]
    fn test_offset() {
        let mut off = OffsetNumC::<i16, 7, 5>::new(3);
        assert_eq!(off.a(), 10);
        off += 1;
        assert_eq!(off.a(), 11);
        off += 1;
        assert_eq!(off.a(), 5);
        off += 1;
        assert_eq!(off.a(), 6);
    }

    #[test]
    fn test_offset_2() {
        let off = OffsetNumC::<usize, 5, 2>::new(1);
        assert_eq!(off.a(), 6);
        for test in [507, 512, 502, 497, 22] {
            let bigoff = OffsetNumC::<usize, 5, 502>::new(test);    
            assert_eq!(bigoff.a(), 502);
        }
    }
}
