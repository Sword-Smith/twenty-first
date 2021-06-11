use ring::digest::{digest, Algorithm, Context, Digest};
use serde::Serialize;

/// The type of values stored in a `MerkleTree` must implement
/// this trait, in order for them to be able to be fed
/// to a Ring `Context` when computing the hash of a leaf.
///
/// A default instance for types that already implements
/// `AsRef<[u8]>` is provided.
///
/// ## Example
///
/// Here is an example of how to implement `Hashable` for a type
/// that does not (or cannot) implement `AsRef<[u8]>`:
///
/// ```ignore
/// impl Hashable for PublicKey {
///     fn update_context(&self, context: &mut Context) {
///         let bytes: Vec<u8> = self.to_bytes();
///         context.update(&bytes);
///     }
/// }
/// ```
pub trait Hashable {
    /// Update the given `context` with `self`.
    ///
    /// See `ring::digest::Context::update` for more information.
    fn update_context(&self, context: &mut Context);
}

// impl<T: AsRef<[u8]>> Hashable for T {
//     fn update_context(&self, context: &mut Context) {
//         context.update(self.as_ref());
//     }
// }

impl<T: Serialize> Hashable for T {
    fn update_context(&self, context: &mut Context) {
        // context.update(self.as_ref());
        // println!(
        //     "bincode::serialize(self) = {:?}",
        //     bincode::serialize(self).unwrap().as_slice()
        // );
        context.update(bincode::serialize(self).unwrap().as_slice());
    }
}

// macro_rules! impl_hashable {
//     ( $($t:ty),* ) => {
//         $( impl Hashable for $t
//     {
//         fn update_context(&self, context: &mut Context) {
//             // let bytes: Vec<u8> = self.to_bytes();
//             let bytes = self.to_be_bytes();
//             context.update(&bytes);
//         }
//     }) *
//     }
// }

// impl_hashable! { i128 }

//  impl Hashable for i128 {
//      fn update_context(self: &i128, context: &mut Context) {
//          // let bytes: Vec<u8> = self.to_bytes();
//          let bytes = self.to_be_bytes();
//          context.update(&bytes);
//      }
//  }

/// The sole purpose of this trait is to extend the standard
/// `ring::algo::Algorithm` type with a couple utility functions.
pub trait HashUtils {
    /// Compute the hash of the empty string
    fn hash_empty(&'static self) -> Digest;

    /// Compute the hash of the given leaf
    fn hash_leaf<T>(&'static self, bytes: &T) -> Digest
    where
        T: Hashable;

    /// Compute the hash of the concatenation of `left` and `right`.
    // XXX: This is overly generic temporarily to make refactoring easier.
    // TODO: Give `left` and `right` type &Digest.
    fn hash_nodes<T>(&'static self, left: &T, right: &T) -> Digest
    where
        T: Hashable;
}

impl HashUtils for Algorithm {
    fn hash_empty(&'static self) -> Digest {
        digest(self, &[])
    }

    fn hash_leaf<T>(&'static self, leaf: &T) -> Digest
    where
        T: Hashable,
    {
        let mut ctx = Context::new(self);
        // ctx.update(&[0x00]); // TODO: include?
        leaf.update_context(&mut ctx);
        ctx.finish()
    }

    fn hash_nodes<T>(&'static self, left: &T, right: &T) -> Digest
    where
        T: Hashable,
    {
        let mut ctx = Context::new(self);
        // ctx.update(&[0x01]); // TODO: include?
        left.update_context(&mut ctx);
        right.update_context(&mut ctx);
        ctx.finish()
    }
}
