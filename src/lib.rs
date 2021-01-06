#![cfg_attr(not(test), no_std)]
//! # Overview
//! ModNum is a highly ergonomic modular arithmetic struct intended for no_std use.
//!
//! ModNum objects represent a value modulo m. The value and modulo can be of any
//! primitive integer type.  Arithmetic operators include +, - (both unary and binary),
//! *, and ==.
//!
//! ModNum was originally developed to facilitate bidirectional navigation through fixed-size
//! arrays at arbitrary starting points. This is facilitated by a double-ended iterator that
//! traverses the entire ring starting at any desired value.
//!
//! Note that ModNum is not designed to work with arbitrary-length integers, as it requires its
//! integer type to implement the Copy trait.
//!
//! For the [2020 Advent of Code](https://adventofcode.com/2020)
//! ([Day 13](https://adventofcode.com/2020/day/13) part 2),
//! I extended ModNum to solve systems of modular equations, provided that each modular equation
//! is represented using signed integers. My implementation is based on this
//! [lucid](https://byorgey.wordpress.com/2020/02/15/competitive-programming-in-haskell-modular-arithmetic-part-1/)
//! [explanation](https://byorgey.wordpress.com/2020/03/03/competitive-programming-in-haskell-modular-arithmetic-part-2/)
//! by [Brent Yorgey](http://ozark.hendrix.edu/~yorgey/).
//!
//! # Arithmetic Examples
//! Addition, subtraction, multiplication, and unary negation are all fully supported for both
//! signed and unsigned integer types. Note that the right-hand side will be an integer of the
//! corresponding type, rather than another ModNum. I have personally found this to be most
//! convenient in practice.
//!
//! ```
//! use bare_metal_modulo::ModNum;
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
//! assert_eq!(m.a(), 2);
//! assert_eq!(m.m(), 5);
//! ```
//!
//! The **==** operator can be used to compare two ModNums or a ModNum and an
//! integer of the corresponding type. In both cases, it represents congruence rather than
//! strict equality.
//!
//! ```
//! use bare_metal_modulo::ModNum;
//!
//! let m = ModNum::new(2, 5);
//! assert!(m == 2);
//! assert!(m == 7);
//! assert!(m == -3);
//! assert!(m != 3);
//! ```
//!
//! # Accessing Values
//! Each ModNum represents an integer **a (mod m)**. To access these values, use the
//! corresponding **a()** and **m()** methods. Note that **a()** will always return a fully
//! reduced value, regardless of how it was initialized.
//!
//! ```
//! use bare_metal_modulo::ModNum;
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
//! ```
//!
//! # Iteration
//! I originally created ModNum to facilitate cyclic iteration through a fixed-size array from an
//! arbitrary starting point in a no_std environment. Its double-ended iterator facilitates
//! both forward and backward iteration.
//!
//! ```
//! use bare_metal_modulo::ModNum;
//!
//! let forward: Vec<usize> = ModNum::new(2, 5).iter().map(|mn| mn.a()).collect();
//! assert_eq!(forward, vec![2, 3, 4, 0, 1]);
//!
//! let reverse: Vec<usize> = ModNum::new(2, 5).iter().rev().map(|mn| mn.a()).collect();
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
//! use bare_metal_modulo::ModNum;
//!
//! let a_values = (2..=4);
//! let m_values = (5..).step_by(2);
//! let mut values = a_values.zip(m_values).map(|(a, m)| ModNum::new(a, m));
//! let solution = ModNum::<i128>::chinese_remainder_system(&mut values).unwrap().a();
//! assert_eq!(solution, 157);
//!
//! let values = vec![ModNum::new(2, 5), ModNum::new(3, 7), ModNum::new(4, 9)];
//! let solution = ModNum::<i128>::chinese_remainder_system(&mut values.iter().copied()).unwrap().a();
//! assert_eq!(solution, 157);
//!
//! let mut values = [(0, 23), (28, 41), (20, 37), (398, 421), (11, 17), (15, 19), (6, 29),
//!                   (433, 487), (11, 13), (5, 137), (19, 49)].iter().copied().map(|(a, m)| ModNum::new(a, m));
//! let solution = ModNum::<i128>::chinese_remainder_system(&mut values).unwrap().a();
//! assert_eq!(solution, 762009420388013796);
//! ```
use core::mem;
use num::{Integer, Signed};
use core::ops::{Add, AddAssign, Sub, SubAssign, Mul, MulAssign, Neg};

/// Represents an integer **a (mod m)**
#[derive(Debug,Copy,Clone,Eq,PartialEq,Ord,PartialOrd)]
pub struct ModNum<N> {
    num: N,
    modulo: N
}

impl <N: Integer+Copy> ModNum<N> {
    /// Creates a new integer **a (mod m)**
    pub fn new(a: N, m: N) -> Self {
        ModNum { num: a.mod_floor(&m), modulo: m }
    }

    /// Returns the integer value **a** for **a (mod m)**
    pub fn a(&self) -> N {
        self.num
    }

    /// Returns the modulo value **m** for **a (mod m)**
    pub fn m(&self) -> N {
        self.modulo
    }

    /// Returns an iterator starting at **a (mod m)** and ending at **a - 1 (mod m)**
    pub fn iter(&self) -> ModNumIterator<N> {
        ModNumIterator::new(*self)
    }
}

impl <N: Integer + Signed + Copy> ModNum<N> {

    /// Solves a pair of modular equations using the [Chinese Remainder Theorem](https://byorgey.wordpress.com/2020/03/03/competitive-programming-in-haskell-modular-arithmetic-part-2/)
    /// This is my translation into Rust of [Brent Yorgey's Haskell implementation](https://byorgey.wordpress.com/2020/03/03/competitive-programming-in-haskell-modular-arithmetic-part-2/).
    ///
    /// - self represents the modular equation x = a (mod m)
    /// - other represents the modular equation x = b (mod n)
    /// - It returns a ModNum corresponding to the equation x = c (mod mn) where
    ///   c $\equiv$ a (mod m) and c $\equiv$ b (mod n)
    pub fn chinese_remainder(&self, other: ModNum<N>) -> ModNum<N> {
        let (g, u, v) = ModNum::egcd(self.modulo, other.modulo);
        let c = (self.num * other.modulo * v + other.num * self.modulo * u).div_floor(&g);
        ModNum::new(c, self.modulo * other.modulo)
    }

    /// Solves a system of modular equations using ModMum::chinese_remainder().
    ///
    /// Each equation in the system is an element of the **modnums** iterator parameter.
    /// - Returns None if the iterator is empty.
    /// - Returns Some(element) if the iterator has only one element.
    /// - Returns Some(solution) if the iterator has two or more elements, where the solution is
    ///   found by repeatedly calling ModNum::chinese_remainder().
    pub fn chinese_remainder_system<I:Iterator<Item=ModNum<N>>>(modnums: &mut I) -> Option<ModNum<N>> {
        modnums.next().map(|start_num|
            modnums.fold(start_num, |a, b| a.chinese_remainder(b)))
    }

    /// [Extended Euclidean Algorithm for Greatest Common Divisor](https://byorgey.wordpress.com/2020/02/15/competitive-programming-in-haskell-modular-arithmetic-part-1/) for GCD.
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

#[derive(Debug)]
pub struct ModNumIterator<N> {
    next: ModNum<N>,
    next_back: ModNum<N>,
    finished: bool
}

impl <N: Integer+Copy> ModNumIterator<N> {
    pub fn new(mn: ModNum<N>) -> Self {
        ModNumIterator {next: mn, next_back: mn - N::one(), finished: false}
    }
}

fn update<N: Integer+Copy, F:Fn(&ModNum<N>,N)->ModNum<N>>(finished: &mut bool, update: &mut ModNum<N>, updater: F, target: ModNum<N>) -> Option<<ModNumIterator<N> as Iterator>::Item> {
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

impl <N: Integer+Copy> Iterator for ModNumIterator<N> {
    type Item = ModNum<N>;

    fn next(&mut self) -> Option<Self::Item> {
        update(&mut self.finished, &mut self.next, |m, u| *m + u, self.next_back)
    }
}

impl <N: Integer+Copy> DoubleEndedIterator for ModNumIterator<N> {
    fn next_back(&mut self) -> Option<Self::Item> {
        update(&mut self.finished, &mut self.next_back, |m, u| *m - u, self.next)
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
    fn test_iter_up() {
        assert_eq!(vec![2, 3, 4, 0, 1], ModNum::new(2, 5).iter().map(|m: ModNum<usize>| m.a()).collect::<Vec<usize>>())
    }

    #[test]
    fn test_iter_down() {
        assert_eq!(vec![1, 0, 4, 3, 2], ModNum::new(2, 5).iter().rev().map(|m: ModNum<usize>| m.a()).collect::<Vec<usize>>())
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
    fn test_big() {
        let mut values = [(0, 23), (28, 41), (20, 37), (398, 421), (11, 17), (15, 19), (6, 29), (433, 487), (11, 13), (5, 137), (19, 49)].iter().copied().map(|(a, m)| ModNum::new(a, m));
        let solution = ModNum::<i128>::chinese_remainder_system(&mut values).unwrap().a();
        println!("solution: {:?}, max i64: {}", solution, i64::MAX);
        assert_eq!(solution, 762009420388013796);
    }
}
