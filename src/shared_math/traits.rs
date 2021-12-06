use std::convert::{From, TryInto};
use std::fmt::{Debug, Display};
use std::hash::Hash;

pub trait IdentityValues {
    fn is_zero(&self) -> bool;
    fn is_one(&self) -> bool;
    fn ring_zero(&self) -> Self;
    fn ring_one(&self) -> Self;
}

pub trait FieldBatchInversion
where
    Self: Sized,
{
    fn batch_inversion(&self, elements: Vec<Self>) -> Vec<Self>;
}

pub trait ModPowU64 {
    fn mod_pow_u64(&self, pow: u64) -> Self;
}

// We *cannot* use the std library From/Into traits as they cannot
// capture which field the new element is a member of.
pub trait New {
    fn new_from_usize(&self, value: usize) -> Self;
}

pub trait FieldElement:
    num_traits::Num
    + Clone
    + Hash
    + Debug
    + Display
    + PartialEq
    + Eq
    + PartialOrd
    + Ord
    + From<i128>
    + TryInto<i128>
{
    fn is_power_of_2(&self) -> bool;
}
