// Copyright(c) The Maintainers of Nanvix.
// Licensed under the MIT License.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(all(test, feature = "std"), feature(random))]
// Verus does not yet support compound assignment on struct fields (e.g., self.usage += 1).
#![allow(clippy::assign_op_pattern)]

//==================================================================================================
// Modules
//==================================================================================================

#[cfg(all(test, feature = "std"))]
mod test;

//==================================================================================================
// Imports
//==================================================================================================

use ::raw_array::RawArray;
#[cfg(verus_keep_ghost)]
use ::raw_array::{
    axiom_u8_zero_is_0,
    is_zero,
};
use ::sys::error::{
    Error,
    ErrorCode,
};
use ::vstd::prelude::*;

// Include specifications.
#[cfg(verus_keep_ghost)]
include!("lib.spec.rs");

// Include proofs.
#[cfg(verus_keep_ghost)]
include!("lib.proof.rs");

// Include verified tests.
#[cfg(verus_keep_ghost)]
include!("lib.test.rs");

//==================================================================================================
// Structures
//==================================================================================================

verus! {

///
/// # Description
///
/// A bitmap.
///
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
#[verifier::ext_equal]
pub struct Bitmap {
    /// Capacity of the bitmap (in bits).
    number_of_bits: usize,
    /// Number of bits set in the bitmap.
    usage: usize,
    /// Underlying bits.
    bits: RawArray<u8>,
    /// Hint: first bit index that might be free. Avoids O(n) rescans.
    next_free: usize,
}

//==================================================================================================
// Implementations
//==================================================================================================

impl Bitmap {
    ///
    /// # Description
    ///
    /// Creates a new bitmap with a given length. The bitmap is initialized with all bits set to zero.
    ///
    /// # Parameters
    ///
    /// - `number_of_bits`: Length of the bitmap in bits.
    ///
    /// # Returns
    ///
    /// Upon success, a new bitmap is returned. Upon failure, an error is returned instead.
    ///
    pub fn new(number_of_bits: usize) -> (result: Result<Self, Error>)
        ensures
            bitmap = result,
                &&& bitmap.inv()
                &&& bitmap@.number_of_bits() == array@.len() * (u8::BITS as int)
                &&& bitmap@.is_empty()
                &&& forall|i: int| 0 <= i < bitmap@.number_of_bits() ==> !bitmap.is_bit_set(i)

    {
        // Check if the length is invalid.
        if number_of_bits == 0 || number_of_bits >= u32::MAX as usize {
            let reason: &str = "invalid length";
            return Err(Error::new(ErrorCode::InvalidArgument, reason));
        }

        // Check if the length is not a multiple of the number of the bitmap word.
        if !number_of_bits.is_multiple_of(u8::BITS as usize) {
            let reason: &str = "length must be a multiple of 8";
            return Err(Error::new(ErrorCode::InvalidArgument, reason));
        }

        // Allocate the bitmap.
        // Note: RawArray::new() guarantees zero-initialization of the backing storage.
        let len: usize = number_of_bits / u8::BITS as usize;
        proof {
            Self::lemma_u8_array_len_fits_isize(len);
        }
        let array: RawArray<u8> = RawArray::new(len)?;

        let result = Self {
            number_of_bits,
            bits: array,
            usage: 0,
            next_free: 0,
        };

        while offset < size
            invariant_except_break
                start == start_before_inner,
                free,
            invariant
                self.inv(),
                old_self.inv(),
                old_self == *old(self),
                0 < size <= self.number_of_bits,
                offset <= size,
                start_before_inner <= self.number_of_bits - size,
                self@.set_bits =~= old(self)@.set_bits,
                checked_before == start_before_inner as int,
                // Positions before start_before_inner are already checked.
                forall|p: int| #![trigger self.has_free_range_at(p, size as int)]
                    (!wrapped ==> initial_start as int <= p < checked_before ==> !self.has_free_range_at(p, size as int)),
                forall|p: int| #![trigger self.has_free_range_at(p, size as int)]
                    (wrapped ==> 0 <= p < checked_before ==> !self.has_free_range_at(p, size as int)),
                free ==> forall|i: int| 0 <= i < offset ==>
                    !#[trigger] self.is_bit_set((start_before_inner + i) as int),
            ensures
                start <= self.number_of_bits,
                free ==> start == start_before_inner && start <= self.number_of_bits - size &&
                    forall|i: int| 0 <= i < size ==>
                        !#[trigger] self.is_bit_set((start + i) as int),
                !free ==> start > start_before_inner,
                !free ==> forall|p: int| #![trigger self.has_free_range_at(p, size as int)]
                    (!wrapped ==> initial_start as int <= p < start as int ==> !self.has_free_range_at(p, size as int)),
                !free ==> forall|p: int| #![trigger self.has_free_range_at(p, size as int)]
                    (wrapped ==> 0 <= p < start as int ==> !self.has_free_range_at(p, size as int)),
            decreases
                size - offset,
        {
            let idx: usize = start + offset;
            let (w, b): (usize, usize) = self.index_unchecked(idx);
            if (self.bits[w] & (1 << b)) != 0 {
                free = false;
                start += offset + 1;
                proof {
                    self.lemma_set_bit_blocks_free_range(
                        start_before_inner as int, idx as int, offset as int, size as int);
                }
                break;
            }
            offset += 1;
        }
        proof {
            Self::lemma_new_bitmap_inv(&result);
        }

        Ok(result)
    }
}
}