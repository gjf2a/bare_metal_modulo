#![cfg_attr(not(test), no_std)]

use core::mem;
use num::Integer;
use core::ops::{Add, AddAssign, Sub, SubAssign};

#[derive(Debug,Copy,Clone,Eq,PartialEq,Ord,PartialOrd)]
pub struct ModNum<N> {
    num: N,
    modulo: N
}

impl <N: Integer+Copy> ModNum<N> {
    pub fn new(num: N, modulo: N) -> Self {
        ModNum {num: num.mod_floor(&modulo), modulo}
    }

    pub fn n(&self) -> N {
        self.num
    }

    pub fn iter(&self) -> ModNumIterator<N> {
        ModNumIterator::new(*self)
    }
}

impl <N:Integer+Copy> Add<N> for ModNum<N> {
    type Output = ModNum<N>;

    fn add(self, rhs: N) -> Self::Output {
        ModNum {num: (self.num + rhs).mod_floor(&self.modulo), modulo: self.modulo}
    }
}

impl <N:Integer+Copy> AddAssign<N> for ModNum<N> {
    fn add_assign(&mut self, rhs: N) {
        *self = *self + rhs;
    }
}

impl <N:Integer+Copy> Sub<N> for ModNum<N> {
    type Output = ModNum<N>;

    fn sub(self, rhs: N) -> Self::Output {
        self + (self.modulo - (rhs.mod_floor(&self.modulo)))
    }
}

impl <N:Integer+Copy> SubAssign<N> for ModNum<N> {
    fn sub_assign(&mut self, rhs: N) {
        *self = *self - rhs;
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
    fn test_sub_u() {
        for (n, m, sub, target) in vec![(1, 5, 2, 4)] {
            assert_eq!(ModNum::new(n, m) - sub, ModNum::new(target, m));
        }
    }

    #[test]
    fn test_iter_up() {
        assert_eq!(vec![2, 3, 4, 0, 1], ModNum::new(2, 5).iter().map(|m: ModNum<usize>| m.n()).collect::<Vec<usize>>())
    }

    #[test]
    fn test_iter_down() {
        assert_eq!(vec![1, 0, 4, 3, 2], ModNum::new(2, 5).iter().rev().map(|m: ModNum<usize>| m.n()).collect::<Vec<usize>>())
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
    }
}
