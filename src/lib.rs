#![cfg_attr(not(test), no_std)]
//! ModNum is a highly ergonomic modular arithmetic struct intended for no_std use.
//!
//! ModNum objects represent a value modulo m. The value and modulo can be of any
//! primitive integer type.  Arithmetic operators include +, -, *, and ==.
//!
//! It can solve systems of modular equations as long as the
//! value and modulo are signed integers.
//!
//!
use core::mem;
use num::{Integer, Signed};
use core::ops::{Add, AddAssign, Sub, SubAssign, Mul, MulAssign, Neg};

#[derive(Debug,Copy,Clone,Eq,PartialEq,Ord,PartialOrd)]
pub struct ModNum<N> {
    num: N,
    modulo: N
}

impl <N: Integer+Copy> ModNum<N> {
    pub fn new(num: N, modulo: N) -> Self {
        ModNum { num: num.mod_floor(&modulo), modulo }
    }

    pub fn a(&self) -> N {
        self.num
    }

    pub fn m(&self) -> N {
        self.modulo
    }

    pub fn iter(&self) -> ModNumIterator<N> {
        ModNumIterator::new(*self)
    }
}

impl <N: Integer + Signed + Copy> ModNum<N> {
    pub fn chinese_remainder(&self, other: ModNum<N>) -> ModNum<N> {
        let (g, u, v) = ModNum::egcd(self.modulo, other.modulo);
        let c = (self.num * other.modulo * v + other.num * self.modulo * u) / g;
        ModNum::new(c, self.modulo * other.modulo)
    }

    pub fn chinese_remainder_system<I:Iterator<Item=ModNum<N>>>(modnums: &mut I) -> Option<ModNum<N>> {
        modnums.next().map(|start_num|
            modnums.fold(start_num, |a, b| a.chinese_remainder(b)))
    }

    pub fn egcd(a: N, b: N) -> (N,N,N) {
        if b == N::zero() {
            (a.signum() * a, a.signum(), N::zero())
        } else {
            let (g, x, y) = ModNum::egcd(b, a.mod_floor(&b));
            (g, y, x - (a / b) * y)
        }
    }
}

// Congruence
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
}
