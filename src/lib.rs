#![feature(const_generics)]
#![cfg_attr(not(test), no_std)]
//! # Overview
//! The bare_metal_modulo crate includes two structs:
//! - ModNum is a highly ergonomic modular arithmetic struct intended for no_std use.
//! - ModNumC is similar to ModNum, but uses [const generics](https://rust-lang.github.io/rfcs/2000-const-generics.html) to specify the modulo.
//! - ModNumIterator is a double-ended iterator that starts with the ModNum upon which it is
//!   invoked, making a complete traversal of the elements in that ModNum's ring.
//!
//! ModNum objects represent a value modulo m. The value and modulo can be of any
//! primitive integer type.  Arithmetic operators include +, - (both unary and binary),
//! *, /, pow(), and ==. Additional capabilities include computing multiplicative inverses
//! and solving modular equations.
//!
//! ModNumC objects likewise represent a value modulo M, where M is a generic constant of the
//! usize type. Arithmetic operators include +, - (both unary and binary), *, and ==.
//!
//! This library was originally developed to facilitate bidirectional navigation through fixed-size
//! arrays at arbitrary starting points. This is facilitated by a double-ended iterator that
//! traverses the entire ring starting at any desired value. The iterator supports both ModNum and
//! ModNumC.
//!
//! Note that ModNum and ModNumC are not designed to work with arbitrary-length integers, as
//! they require their integer type to implement the Copy trait.
//!
//! For the [2020 Advent of Code](https://adventofcode.com/2020)
//! ([Day 13](https://adventofcode.com/2020/day/13) part 2),
//! I extended ModNum to solve systems of modular equations, provided that each modular equation
//! is represented using signed integers. My implementation is based on this
//! [lucid](https://byorgey.wordpress.com/2020/02/15/competitive-programming-in-haskell-modular-arithmetic-part-1/)
//! [explanation](https://byorgey.wordpress.com/2020/03/03/competitive-programming-in-haskell-modular-arithmetic-part-2/)
//! by [Brent Yorgey](http://ozark.hendrix.edu/~yorgey/).
//!
//! # Accessing Values
//! Each ModNum/ModNumC represents an integer **a (mod m)**. To access these values, use the
//! corresponding **a()** and **m()** methods. Note that **a()** will always return a fully
//! reduced value, regardless of how it was initialized.
//!
//! ```
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
//! ```
//!
//! # Arithmetic
//! Addition, subtraction, and multiplication are all fully supported for both
//! signed and unsigned integer types. The right-hand side may either be an integer of the
//! corresponding type or another ModNum. In the latter case, if the modulo values differ
//! it will **panic**. For a ModNumC, there is no risk of a panic, as any disparity will be
//! flagged at compile time.
//!
//! Unary negation is supported for both signed and unsigned integers.
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
//! ```
//!
//! Saturating addition and subtraction are often useful relative to the modulus, so the
//! [`num::Saturating`](https://docs.rs/num/0.3.1/num/trait.Saturating.html) trait is implemented
//! as well.
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
//! As inverses are only defined when **a** and **m** are relatively prime, **.inverse()** will return
//! **None** when it is not possible to calculate.
//!
//! Division is defined in terms of the multiplicative inverse, so it is likewise only supported for
//! signed integers, and will return **None** when the quotient does not exist. Assigned division (/=)
//! will **panic** if the quotient does not exist.
//!
//! The **.pow()** method is fully supported for unsigned integer types. It also works for signed integer
//! types, but it will **panic** if given a negative exponent. If negative exponents are possible,
//! use **.pow_signed()**, which will return **None** if the result does not exist.
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
//! ```
//!
//! The **==** operator can be used to compare two ModNums, two ModNumCs or a ModNum/ModNumC and an
//! integer of the corresponding type. In both cases, it represents congruence rather than
//! strict equality.
//!
//! ```
//! use bare_metal_modulo::*;
//!
//! let m = ModNum::new(2, 5);
//! assert!(m == 2);
//! assert!(m == 7);
//! assert!(m == -3);
//! assert!(m != 3);
//!
//! let m: ModNumC<i32,5> = ModNumC::new(2);
//! assert!(m == 2);
//! assert!(m == 7);
//! assert!(m == -3);
//! assert!(m != 3);
//! ```
//!
//! # Iteration
//! I originally created ModNum to facilitate cyclic iteration through a fixed-size array from an
//! arbitrary starting point in a no_std environment. Its double-ended iterator facilitates
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
//! # Solving Modular Equations with the Chinese Remainder Theorem
//! For the [2020 Advent of Code](https://adventofcode.com/2020)
//! ([Day 13](https://adventofcode.com/2020/day/13) part 2),
//! I extended ModNum to solve systems of modular equations, provided that each modular equation
//! is represented using signed integers. My implementation is based on this
//! [lucid](https://byorgey.wordpress.com/2020/02/15/competitive-programming-in-haskell-modular-arithmetic-part-1/)
//! [explanation](https://byorgey.wordpress.com/2020/03/03/competitive-programming-in-haskell-modular-arithmetic-part-2/)
//! by [Brent Yorgey](http://ozark.hendrix.edu/~yorgey/).
//!
//! The solver works directly with an iterator containing the ModNum objects corresponding to the
//! modular equations to be solved, facilitating space-efficient solutions of a sequence coming
//! from a stream. The examples below show two variants of the same system. The first example uses
//! an iterator, and the second example retrieves the system from a Vec.
//!
//! Note that the solution value can rapidly become large, as shown in the third example. I
//! recommend using **i128**, so as to maximize the set of solvable equations given this library's
//! constraint of using **Copy** integers only. While the solution to the third example is
//! representable as an **i64**, some of the intermediate multiplications will overflow unless
//! **i128** is used.
//!
//! ```
//! use bare_metal_modulo::*;
//!
//! let mut values = (2..).zip((5..).step_by(2)).map(|(a, m)| ModNum::new(a, m)).take(3);
//! let solution = ModNum::<i128>::chinese_remainder_system(&mut values);
//! assert_eq!(solution.unwrap().a(), 157);
//!
//! let values = vec![ModNum::new(2, 5), ModNum::new(3, 7), ModNum::new(4, 9)];
//! let solution = ModNum::<i128>::chinese_remainder_system(&mut values.iter().copied());
//! assert_eq!(solution.unwrap().a(), 157);
//!
//!let mut values = [(0, 23), (28, 41), (20, 37), (398, 421), (11, 17), (15, 19), (6, 29),
//!    (433, 487), (11, 13), (5, 137), (19, 49)]
//!    .iter().copied().map(|(a, m)| ModNum::new(a, m));
//! let solution = ModNum::<i128>::chinese_remainder_system(&mut values);
//! assert_eq!(solution.unwrap().a(), 762009420388013796);
//! ```
use core::mem;
use num::{Integer, Signed, NumCast, FromPrimitive};
use core::ops::{Add, AddAssign, Sub, SubAssign, Mul, MulAssign, Neg, Div, DivAssign};
use num::traits::{Pow, SaturatingAdd, SaturatingSub};
use core::fmt::{Debug, Display, Formatter};

pub trait MNum : Copy + Eq + PartialEq {
    type Num: Integer + Copy;
    fn a(&self) -> Self::Num;
    fn m(&self) -> Self::Num;
}

/// Represents an integer **a (mod m)**
#[derive(Debug,Copy,Clone,Eq,PartialEq,Ord,PartialOrd)]
pub struct ModNum<N> {
    num: N,
    modulo: N
}

impl <N:Integer+Copy> MNum for ModNum<N> {
    type Num = N;

    fn a(&self) -> N {
        self.num
    }

    fn m(&self) -> N {
        self.modulo
    }
}

impl <N: Integer+Copy> ModNum<N> {
    /// Creates a new integer **a (mod m)**
    pub fn new(a: N, m: N) -> Self {
        ModNum { num: a.mod_floor(&m), modulo: m }
    }

    /// Returns an iterator starting at **a (mod m)** and ending at **a - 1 (mod m)**
    pub fn iter(&self) -> ModNumIterator<N,Self> {
        ModNumIterator::new(*self)
    }
}

impl <N:Display+Integer+Copy> Display for ModNum<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{} (mod {})", self.a(), self.m())
    }
}

impl <N: Integer + Signed + Copy + NumCast> ModNum<N> {

    /// Solves a pair of modular equations using the [Chinese Remainder Theorem](https://byorgey.wordpress.com/2020/03/03/competitive-programming-in-haskell-modular-arithmetic-part-2/).
    ///
    /// This is my translation into Rust of [Brent Yorgey's Haskell implementation](https://byorgey.wordpress.com/2020/03/03/competitive-programming-in-haskell-modular-arithmetic-part-2/).
    ///
    /// - self represents the modular equation **x = a (mod m)**
    /// - other represents the modular equation **x = b (mod n)**
    /// - It returns a ModNum corresponding to the equation **x = c (mod mn)** where
    ///   **c** is congruent both to **a (mod m)** and **b (mod n)**
    pub fn chinese_remainder(&self, other: ModNum<N>) -> ModNum<N> {
        let (g, u, v) = ModNum::egcd(self.modulo, other.modulo);
        let c = (self.num * other.modulo * v + other.num * self.modulo * u).div_floor(&g);
        ModNum::new(c, self.modulo * other.modulo)
    }

    /// Solves a system of modular equations using ModMum::chinese_remainder().
    ///
    /// Each equation in the system is an element of the **modnums** iterator parameter.
    /// - Returns **None** if the iterator is empty.
    /// - Returns **Some(element)** if the iterator has only one element.
    /// - Returns **Some(solution)** if the iterator has two or more elements, where the solution is
    ///   found by repeatedly calling **ModNum::chinese_remainder()**.
    pub fn chinese_remainder_system<I:Iterator<Item=ModNum<N>>>(modnums: &mut I) -> Option<ModNum<N>> {
        modnums.next().map(|start_num|
            modnums.fold(start_num, |a, b| a.chinese_remainder(b)))
    }

    /// [Extended Euclidean Algorithm for Greatest Common Divisor](https://byorgey.wordpress.com/2020/02/15/competitive-programming-in-haskell-modular-arithmetic-part-1/) for GCD.
    ///
    /// This is my translation into Rust of [Brent Yorgey's Haskell implementation](https://byorgey.wordpress.com/2020/02/15/competitive-programming-in-haskell-modular-arithmetic-part-1/).
    ///
    /// Given two integers **a** and **b**, it returns three integer values:
    /// - Greatest Common Divisor (**g**) of **a** and **b**
    /// - Two additional values **x** and **y**, where **ax + by = g**
    pub fn egcd(a: N, b: N) -> (N,N,N) {
        if b == N::zero() {
            (a.signum() * a, a.signum(), N::zero())
        } else {
            let (g, x, y) = ModNum::egcd(b, a.mod_floor(&b));
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
    pub fn inverse(&self) -> Option<ModNum<N>> {
        let (g, _, inv) = ModNum::<N>::egcd(self.m(), self.a());
        if g == N::one() {Some(ModNum::new(inv, self.m()))} else {None}
    }

    /// Returns Some(a^rhs (mod m)). Handles negative exponents correctly, unlike .pow().
    /// Returns None if the inverse is undefined.
    pub fn pow_signed(&self, rhs: N) -> Option<ModNum<N>> {
        if rhs < N::zero() {
            self.pow(-rhs).inverse()
        } else {
            Some(self.pow(rhs))
        }
    }
}

/// Returns **true** if **other** is congruent to **self.a() (mod self.m())**
impl <N:Integer+Copy> PartialEq<N> for ModNum<N> {
    fn eq(&self, other: &N) -> bool {
        self.num == other.mod_floor(&self.modulo)
    }
}

impl <N:Integer+Copy> Add<N> for ModNum<N> {
    type Output = ModNum<N>;

    fn add(self, rhs: N) -> Self::Output {
        ModNum::new(self.num + rhs, self.modulo)
    }
}

impl <N:Integer+Copy> AddAssign<N> for ModNum<N> {
    fn add_assign(&mut self, rhs: N) {
        *self = *self + rhs;
    }
}

impl <N:Integer+Copy+Debug> Add<ModNum<N>> for ModNum<N> {
    type Output = ModNum<N>;

    fn add(self, rhs: ModNum<N>) -> Self::Output {
        assert_eq!(self.m(), rhs.m());
        self + rhs.a()
    }
}

impl <N:Integer+Copy+Debug> AddAssign<ModNum<N>> for ModNum<N> {
    fn add_assign(&mut self, rhs: ModNum<N>) {
        assert_eq!(self.m(), rhs.m());
        *self = *self + rhs.a();
    }
}

impl <N:Integer+Copy> Neg for ModNum<N> {
    type Output = ModNum<N>;

    fn neg(self) -> Self::Output {
        ModNum::new(self.modulo - self.num, self.modulo)
    }
}

impl <N:Integer+Copy> Sub<N> for ModNum<N> {
    type Output = ModNum<N>;

    fn sub(self, rhs: N) -> Self::Output {
        self + (-ModNum::new(rhs, self.modulo)).a()
    }
}

impl <N:Integer+Copy> SubAssign<N> for ModNum<N> {
    fn sub_assign(&mut self, rhs: N) {
        *self = *self - rhs;
    }
}

impl <N:Integer+Copy+Debug> Sub<ModNum<N>> for ModNum<N> {
    type Output = ModNum<N>;

    fn sub(self, rhs: ModNum<N>) -> Self::Output {
        assert_eq!(self.m(), rhs.m());
        self - rhs.a()
    }
}

impl <N:Integer+Copy+Debug> SubAssign<ModNum<N>> for ModNum<N> {
    fn sub_assign(&mut self, rhs: ModNum<N>) {
        assert_eq!(self.m(), rhs.m());
        *self += -rhs;
    }
}

impl <N:Integer+Copy> Mul<N> for ModNum<N> {
    type Output = ModNum<N>;

    fn mul(self, rhs: N) -> Self::Output {
        ModNum::new(self.num * rhs, self.modulo)
    }
}

impl <N:Integer+Copy> MulAssign<N> for ModNum<N> {
    fn mul_assign(&mut self, rhs: N) {
        *self = *self * rhs;
    }
}

impl <N:Integer+Copy+Debug> Mul<ModNum<N>> for ModNum<N> {
    type Output = ModNum<N>;

    fn mul(self, rhs: ModNum<N>) -> Self::Output {
        assert_eq!(self.m(), rhs.m());
        self * rhs.a()
    }
}

impl <N:Integer+Copy+Debug> MulAssign<ModNum<N>> for ModNum<N> {
    fn mul_assign(&mut self, rhs: ModNum<N>) {
        assert_eq!(self.m(), rhs.m());
        *self = *self * rhs.a();
    }
}

impl <N:Integer+Copy+Signed+NumCast> Div<N> for ModNum<N> {
    type Output = Option<ModNum<N>>;

    fn div(self, rhs: N) -> Self::Output {
        ModNum::new(rhs, self.m()).inverse().map(|inv| self * inv.a())
    }
}

impl <N:Integer+Copy+Signed+NumCast> DivAssign<N> for ModNum<N> {

    /// Performs division in place.
    /// Panics if the quotient is undefined.
    fn div_assign(&mut self, rhs: N) {
        *self = (*self / rhs).unwrap();
    }
}

impl <N:Integer+Copy+Signed+NumCast+Debug> Div<ModNum<N>> for ModNum<N> {
    type Output = Option<ModNum<N>>;

    fn div(self, rhs: ModNum<N>) -> Self::Output {
        assert_eq!(self.m(), rhs.m());
        self / rhs.a()
    }
}

impl <N:Integer+Copy+Signed+NumCast+Debug> DivAssign<ModNum<N>> for ModNum<N> {

    /// Performs division in place.
    /// Panics if the quotient is undefined.
    fn div_assign(&mut self, rhs: ModNum<N>) {
        assert_eq!(self.m(), rhs.m());
        *self = (*self / rhs.a()).unwrap();
    }
}

impl <N:Integer+Copy+NumCast> Pow<N> for ModNum<N> {
    type Output = ModNum<N>;

    /// Returns a^rhs (mod m), for rhs >= 0.
    /// Implements efficient modular exponentiation by [repeated squaring](https://byorgey.wordpress.com/2020/02/15/competitive-programming-in-haskell-modular-arithmetic-part-1/).
    ///
    /// Panics if rhs < 0. If negative exponents are possible, use .pow_signed()
    fn pow(self, rhs: N) -> Self::Output {
        if rhs < N::zero() {
            panic!("Negative exponentiation undefined for ModNum.pow(). Try .pow_signed() instead.")
        } else if rhs == N::zero() {
            ModNum::new(N::one(), self.m())
        } else {
            let r = self.pow(rhs.div_floor(&(N::from(2).unwrap())));
            let mut sq = r * r.a();
            if rhs.is_odd() {
                sq *= self.a();
            }
            sq
        }
    }
}

impl <N:Integer+Copy+NumCast+Debug> Pow<ModNum<N>> for ModNum<N> {
    type Output = ModNum<N>;

    fn pow(self, rhs: ModNum<N>) -> Self::Output {
        assert_eq!(self.m(), rhs.m());
        self.pow(rhs.a())
    }
}

/// A double-ended iterator that starts with the ModNum upon which it is invoked,
/// making a complete traversal of the elements in that ModNum's ring.
#[derive(Debug)]
pub struct ModNumIterator<N:Integer+Copy,M:MNum<Num=N> + Add<N,Output=M> + Sub<N,Output=M>> {
    next: M,
    next_back: M,
    finished: bool
}

impl <N: Integer+Copy,M:MNum<Num=N> + Add<N,Output=M> + Sub<N,Output=M>> ModNumIterator<N,M> {
    pub fn new(mn: M) -> Self {
        ModNumIterator {next: mn, next_back: mn - N::one(), finished: false}
    }
}

fn update<N: Integer+Copy, M:MNum<Num=N> + Add<N,Output=M> + Sub<N,Output=M>, F:Fn(&M,N)->M>(finished: &mut bool, update: &mut M, updater: F, target: M) -> Option<<ModNumIterator<N,M> as Iterator>::Item> {
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

impl <N: Integer+Copy, M:MNum<Num=N> + Add<N,Output=M> + Sub<N,Output=M>> Iterator for ModNumIterator<N,M> {
    type Item = M;

    fn next(&mut self) -> Option<Self::Item> {
        update(&mut self.finished, &mut self.next, |m, u| *m + u, self.next_back)
    }
}

impl <N: Integer+Copy, M:MNum<Num=N> + Add<N,Output=M> + Sub<N,Output=M>> DoubleEndedIterator for ModNumIterator<N,M> {
    fn next_back(&mut self) -> Option<Self::Item> {
        update(&mut self.finished, &mut self.next_back, |m, u| *m - u, self.next)
    }
}

impl <N: Integer+Copy+Debug+Display> SaturatingAdd for ModNum<N> {
    fn saturating_add(&self, v: &Self) -> Self {
        assert_eq!(self.m(), v.m());
        if self.a() + v.a() >= self.m() {
            ModNum::new(self.m() - N::one(), self.m())
        } else {
            *self + *v
        }
    }
}

impl <N: Integer+Copy+Debug+Display> SaturatingSub for ModNum<N> {
    fn saturating_sub(&self, v: &Self) -> Self {
        assert_eq!(self.m(), v.m());
        if self.a() < v.a() {
            ModNum::new(N::zero(), self.m())
        } else {
            *self - *v
        }
    }
}

/// Represents an integer **a (mod M)**
#[derive(Debug,Copy,Clone,Eq,PartialEq,Ord,PartialOrd)]
pub struct ModNumC<N, const M: usize> {
    num: N
}

impl <N:Display, const M: usize> Display for ModNumC<N,M> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{} (mod {})", self.num, M)
    }
}

impl <N:Copy+Integer+FromPrimitive, const M: usize> MNum for ModNumC<N,M> {
    type Num = N;

    fn a(&self) -> Self::Num {
        self.num
    }

    fn m(&self) -> Self::Num {
        N::from_usize(M).unwrap()
    }
}

impl <N:Copy+Integer+FromPrimitive, const M: usize> ModNumC<N,M> {
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

/// Returns **true** if **other** is congruent to **self.a() (mod self.m())**
impl <N:Integer+Copy+FromPrimitive, const M: usize> PartialEq<N> for ModNumC<N,M> {
    fn eq(&self, other: &N) -> bool {
        *self == ModNumC::new(*other)
    }
}

impl <N:Integer+Copy+FromPrimitive, const M: usize> Add<N> for ModNumC<N,M> {
    type Output = ModNumC<N,M>;

    fn add(self, rhs: N) -> Self::Output {
        ModNumC::new(self.num + rhs)
    }
}

impl <N:Integer+Copy+FromPrimitive, const M: usize> AddAssign<N> for ModNumC<N,M> {
    fn add_assign(&mut self, rhs: N) {
        *self = *self + rhs;
    }
}

impl <N:Integer+Copy+FromPrimitive, const M: usize> Add<ModNumC<N,M>> for ModNumC<N,M> {
    type Output = ModNumC<N,M>;

    fn add(self, rhs: ModNumC<N,M>) -> Self::Output {
        self + rhs.a()
    }
}

impl <N:Integer+Copy+FromPrimitive, const M: usize> AddAssign<ModNumC<N,M>> for ModNumC<N,M> {
    fn add_assign(&mut self, rhs: ModNumC<N,M>) {
        *self = *self + rhs.a();
    }
}

impl <N:Integer+Copy+FromPrimitive, const M: usize> Neg for ModNumC<N,M> {
    type Output = ModNumC<N,M>;

    fn neg(self) -> Self::Output {
        ModNumC::new(self.m() - self.num)
    }
}

impl <N:Integer+Copy+FromPrimitive, const M: usize> Sub<N> for ModNumC<N,M> {
    type Output = ModNumC<N,M>;

    fn sub(self, rhs: N) -> Self::Output {
        self + (-ModNumC::new(rhs))
    }
}

impl <N:Integer+Copy+FromPrimitive, const M: usize> SubAssign<N> for ModNumC<N,M> {
    fn sub_assign(&mut self, rhs: N) {
        *self = *self - rhs;
    }
}

impl <N:Integer+Copy+FromPrimitive, const M: usize> Sub<ModNumC<N,M>> for ModNumC<N,M> {
    type Output = ModNumC<N,M>;

    fn sub(self, rhs: ModNumC<N,M>) -> Self::Output {
        self - rhs.a()
    }
}

impl <N:Integer+Copy+FromPrimitive, const M: usize> SubAssign<ModNumC<N,M>> for ModNumC<N,M> {
    fn sub_assign(&mut self, rhs: ModNumC<N,M>) {
        *self += -rhs;
    }
}

impl <N:Integer+Copy+FromPrimitive, const M: usize> Mul<N> for ModNumC<N,M> {
    type Output = ModNumC<N,M>;

    fn mul(self, rhs: N) -> Self::Output {
        ModNumC::new(self.num * rhs)
    }
}

impl <N:Integer+Copy+FromPrimitive, const M: usize> MulAssign<N> for ModNumC<N,M> {
    fn mul_assign(&mut self, rhs: N) {
        *self = *self * rhs;
    }
}

impl <N:Integer+Copy+FromPrimitive, const M: usize> Mul<ModNumC<N,M>> for ModNumC<N,M> {
    type Output = ModNumC<N,M>;

    fn mul(self, rhs: ModNumC<N,M>) -> Self::Output {
        self * rhs.a()
    }
}

impl <N:Integer+Copy+FromPrimitive, const M: usize> MulAssign<ModNumC<N,M>> for ModNumC<N,M> {
    fn mul_assign(&mut self, rhs: ModNumC<N,M>) {
        *self = *self * rhs.a();
    }
}

impl <N: Integer+Copy+FromPrimitive, const M: usize> SaturatingAdd for ModNumC<N,M> {
    fn saturating_add(&self, v: &Self) -> Self {
        if self.a() + v.a() >= self.m() {
            ModNumC::new(self.m() - N::one())
        } else {
            *self + *v
        }
    }
}

impl <N: Integer+Copy+FromPrimitive, const M: usize> SaturatingSub for ModNumC<N,M> {
    fn saturating_sub(&self, v: &Self) -> Self {
        if self.a() < v.a() {
            ModNumC::new(N::zero())
        } else {
            *self - *v
        }
    }
}

#[cfg(test)]
mod tests {
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
        }    }

    #[test]
    fn test_iter_up() {
        assert_eq!(vec![2, 3, 4, 0, 1], ModNum::new(2, 5).iter().map(|m: ModNum<usize>| m.a()).collect::<Vec<usize>>())
    }

    #[test]
    fn test_iter_down() {
        assert_eq!(vec![1, 0, 4, 3, 2], ModNum::new(2, 5).iter().rev().map(|m: ModNum<usize>| m.a()).collect::<Vec<usize>>())
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
}
