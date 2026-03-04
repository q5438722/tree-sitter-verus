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
            result is Ok ==> {
                let bitmap = result->Ok_0;
                &&& bitmap.inv()
                &&& bitmap@.number_of_bits() == number_of_bits as int
                &&& bitmap@.is_empty()
                &&& forall|i: int| 0 <= i < bitmap@.number_of_bits() ==> !bitmap.is_bit_set(i)
            },
            (number_of_bits == 0 ||
             number_of_bits >= u32::MAX as usize ||
             number_of_bits % (u8::BITS as usize) != 0) ==> result is Err,
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

        proof {
            Self::lemma_new_bitmap_inv(&result);
        }

        Ok(result)
    }

    ///
    /// # Description
    ///
    /// Creates a new bitmap from a raw array. The bitmap is initialized with
    /// all bits set to zero.
    ///
    /// # Parameters
    ///
    /// - `array`: Raw array to create the bitmap from.
    ///
    /// # Returns
    ///
    /// Upon success, a new bitmap is returned. Upon failure, an error is returned instead.
    ///
    /// # Errors
    ///
    /// - `InvalidArgument` if the array length multiplied by 8 overflows `usize`.
    ///
    pub fn from_raw_array(array: RawArray<u8>) -> (result: Result<Self, Error>)
        requires
            array@.len() > 0,
            array@.len() * (u8::BITS as usize) < u32::MAX as usize,
            forall|i: int| 0 <= i < array@.len() ==> array@[i] == 0,
        ensures
            result is Ok ==> {
                let bitmap = result->Ok_0;
                &&& bitmap.inv()
                &&& bitmap@.number_of_bits() == array@.len() * (u8::BITS as int)
                &&& bitmap@.is_empty()
                &&& forall|i: int| 0 <= i < bitmap@.number_of_bits() ==> !bitmap.is_bit_set(i)
            },
            // Liveness: given preconditions, always succeeds.
            result is Ok,
    {
        // TODO: remove this runtime check once all callers are verified.
        let number_of_bits: usize = match array.len().checked_mul(u8::BITS as usize) {
            Some(n) => n,
            None => {
                let reason: &str = "bitmap size overflow: array too large";
                return Err(Error::new(ErrorCode::InvalidArgument, reason));
            },
        };

        let result = Self {
            number_of_bits,
            bits: array,
            usage: 0,
            next_free: 0,
        };
        proof {
            result.lemma_zero_bytes_means_empty_set();
            Self::lemma_empty_set_finite();
        }
        Ok(result)
    }

    ///
    /// # Description
    ///
    /// Returns the number of bits in the bitmap.
    ///
    /// # Returns
    ///
    /// The number of bits in the bitmap.
    ///
    pub fn number_of_bits(&self) -> (result: usize)
        requires
            self.inv(),
        ensures
            result as int == self@.number_of_bits(),
            result > 0,
            result < u32::MAX as usize,
    {
        self.number_of_bits
    }

    ///
    /// # Description
    ///
    /// Allocates a bit in the bitmap.
    ///
    /// # Returns
    ///
    /// Upon success, the index of the allocated bit is returned. Upon failure, an error is returned
    /// instead.
    ///
    pub fn alloc(&mut self) -> (result: Result<usize, Error>)
        requires
            old(self).inv(),
        ensures
            self.inv(),
            result is Ok ==> {
                let index = result->Ok_0 as int;
                &&& 0 <= index < self@.number_of_bits()
                &&& self@.number_of_bits() == old(self)@.number_of_bits()
                &&& self.is_bit_set(index)
                &&& !old(self).is_bit_set(index)
                &&& !old(self)@.is_full()
                // Frame: only the allocated bit changed.
                &&& forall|i: int| 0 <= i < self@.number_of_bits() && i != index ==>
                    self.is_bit_set(i) == old(self).is_bit_set(i)
                // Set-based frame.
                &&& self@.set_bits =~= old(self)@.set_bits.insert(index)
                &&& self@.usage() == old(self)@.usage() + 1
            },
            result is Err ==> self@ == old(self)@,
            old(self)@.has_free_bit() ==> result is Ok,
    {
        proof {
            if old(self)@.has_free_bit() {
                old(self).lemma_has_free_bit_implies_exists_free_range_1();
            }
        }
        self.alloc_range(1)
    }

    ///
    /// # Description
    ///
    /// Allocates a range of bits in the bitmap.
    ///
    /// # Parameters
    ///
    /// - `size`: Size of the range to allocate.
    ///
    /// # Returns
    ///
    /// Upon success, the index of the allocated range is returned. Upon failure, an error is returned
    /// instead.
    ///
    pub fn alloc_range(&mut self, size: usize) -> (result: Result<usize, Error>)
        requires
            old(self).inv(),
            size > 0,
            size <= old(self)@.number_of_bits(),
        ensures
            self.inv(),
            result is Ok ==> {
                let start = result->Ok_0 as int;
                &&& 0 <= start < self@.number_of_bits()
                &&& 0 < size <= self@.number_of_bits()
                &&& start + (size as int) <= self@.number_of_bits()
                &&& self@.number_of_bits() == old(self)@.number_of_bits()
                &&& self.all_bits_set_in_range(start, start + (size as int))
                &&& old(self).all_bits_unset_in_range(start, start + (size as int))
                // Frame: only the allocated range changed.
                &&& forall|i: int| 0 <= i < self@.number_of_bits() &&
                    (i < start || i >= start + (size as int)) ==>
                    self.is_bit_set(i) == old(self).is_bit_set(i)
                // Set-based frame.
                &&& self@.set_bits =~= old(self)@.set_bits.union(BitmapView::range_set(start, start + (size as int)))
                &&& self@.usage() == old(self)@.usage() + (size as int)
            },
            result is Err ==> self@ == old(self)@,
            old(self).exists_contiguous_free_range(size as int) ==> result is Ok,
    {
        let ghost old_self = *self;

        // TODO: remove this runtime check once all callers are verified.
        // Check if the size is valid.
        if size == 0 || size > self.number_of_bits {
            proof {
                if size > self.number_of_bits {
                    old_self.lemma_no_free_range_when_size_exceeds(size as int);
                }
            }
            let reason: &str = "invalid size";
            return Err(Error::new(ErrorCode::InvalidArgument, reason));
        }

        // Check if allocation exceeds the bitmap capacity.
        if self.usage > self.number_of_bits - size {
            proof {
                old_self.lemma_no_free_range_when_usage_exceeds(size as int);
            }
            let reason: &str = "allocation exceeds bitmap capacity";
            return Err(Error::new(ErrorCode::OutOfMemory, reason));
        }

        // Note: debug_assert_eq! is not supported by Verus, so we guard it
        // with cfg. The invariant self.inv() already proves this property.
        #[cfg(not(verus_keep_ghost))]
        debug_assert_eq!(
            self.bits.len() * u8::BITS as usize,
            self.number_of_bits,
            "bitmap length must match the number of bits"
        );

        let initial_start: usize = self.next_free;
        let mut start: usize = initial_start;
        let mut wrapped: bool = false;
        let mut done: bool = false;

        // Traverse the bitmap, wrapping around once if needed.
        while !done
            invariant
                self.inv(),
                old_self.inv(),
                old_self == *old(self),
                size > 0,
                size <= self.number_of_bits,
                start <= self.number_of_bits,
                self@.set_bits =~= old(self)@.set_bits,
                self.usage <= self.number_of_bits - size,
                self.number_of_bits == old_self.number_of_bits,
                initial_start as int <= self@.number_of_bits(),
                // Wrap-around state consistency.
                !wrapped ==> start >= initial_start,
                wrapped ==> initial_start > 0,
                // Checked positions.
                !wrapped ==> forall|p: int| #![trigger self.has_free_range_at(p, size as int)]
                    initial_start as int <= p < start as int ==> !self.has_free_range_at(p, size as int),
                wrapped ==> forall|p: int| #![trigger self.has_free_range_at(p, size as int)]
                    initial_start as int <= p < self@.number_of_bits() ==> !self.has_free_range_at(p, size as int),
                wrapped ==> forall|p: int| #![trigger self.has_free_range_at(p, size as int)]
                    0 <= p < start as int ==> !self.has_free_range_at(p, size as int),
                // When done, all positions have been checked.
                done ==> forall|p: int| #![trigger self.has_free_range_at(p, size as int)]
                    0 <= p < self@.number_of_bits() ==> !self.has_free_range_at(p, size as int),
            decreases
                (if !done { 1int } else { 0int }),
                (if !wrapped { 1int } else { 0int }),
                self.number_of_bits - start,
        {
            // Stop condition: exceeded the last valid starting position.
            if start > self.number_of_bits - size {
                // If we haven't wrapped yet and started past 0, retry from beginning.
                if !wrapped && initial_start > 0 {
                    proof {
                        self.lemma_phase1_complete_no_free_range(
                            initial_start as int, start as int, size as int);
                    }
                    start = 0;
                    wrapped = true;
                } else {
                    proof {
                        self.lemma_all_positions_no_free_range(
                            initial_start as int, start as int, size as int, wrapped);
                    }
                    done = true;
                }
            }

            // After wrap-around, stop if we've reached the initial position.
            if !done && wrapped && start >= initial_start {
                proof {
                    self.lemma_all_positions_no_free_range(
                        initial_start as int, start as int, size as int, wrapped);
                }
                done = true;
            }

            if !done {
                // Check for fast-skip path.
                let is_aligned: bool = start.is_multiple_of(u8::BITS as usize);
                if is_aligned {
                    let word: usize = start / u8::BITS as usize;
                    // Fast skip: if the starting word is full, skip to the next word.
                    if self.bits[word] == u8::MAX {
                        proof {
                            self.lemma_full_byte_no_free_range(start as int, size as int);
                        }
                        start += u8::BITS as usize;
                        continue;
                    }
                }

                // Check if all bits in the range are free.
                let ghost start_before_inner: usize = start;
                let mut offset: usize = 0;
                let mut free: bool = true;

                // Ghost: snapshot the "checked before" region for the inner loop.
                let ghost checked_before: int = start as int;

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

                if free {
                    // Found a free range at [start, start + size).
                    proof {
                        self.lemma_free_range_was_unset_in_old(&old_self, start as int, size as int);
                        assert(old(self).all_bits_unset_in_range(start as int, start as int + (size as int)));
                    }
                    // Allocate the range.
                    let ghost pre_alloc_self = *self;
                    let mut alloc_offset: usize = 0;

                    proof {
                        assert(self@.number_of_bits() == old_self@.number_of_bits());
                        assert(pre_alloc_self@.number_of_bits() == old_self@.number_of_bits());
                    }

                    // Verus note: `for offset in 0..size` is not supported;
                    // `self.bits[w] |= 1 << b` is not supported for mutable index.
                    while alloc_offset < size
                        invariant
                            self.bits@.len() == pre_alloc_self.bits@.len(),
                            self.bits@.len() == old_self.bits@.len(),
                            self@.number_of_bits() > 0,
                            self@.number_of_bits() == self.bits@.len() * (u8::BITS as int),
                            self.number_of_bits == pre_alloc_self.number_of_bits,
                            self.number_of_bits as int == self@.number_of_bits(),
                            self.usage == pre_alloc_self.usage,
                            old_self.inv(),
                            pre_alloc_self.inv(),
                            old_self == *old(self),
                            0 < size <= self.number_of_bits,
                            start <= self.number_of_bits - size,
                            alloc_offset <= size,
                            forall|i: int| 0 <= i < alloc_offset ==>
                                #[trigger] self.is_bit_set((start + i) as int),
                            forall|i: int| (0 <= i < self@.number_of_bits() &&
                                (i < start as int || i >= (start + alloc_offset) as int)) ==>
                                #[trigger] self.is_bit_set(i) == #[trigger] old_self.is_bit_set(i),
                            self@.set_bits =~= old_self@.set_bits.union(BitmapView::range_set(start as int, start as int + (alloc_offset as int))),
                            self@.set_bits.finite(),
                            old_self.all_bits_unset_in_range(start as int, start as int + (size as int)),
                        decreases
                            size - alloc_offset,
                    {
                        let idx: usize = start + alloc_offset;
                        let (w, b): (usize, usize) = self.index_unchecked(idx);
                        let ghost loop_old_self = *self;

                        self.bits.set(w, self.bits[w] | (1 << b));

                        proof {
                            loop_old_self.lemma_byte_or_reflects_in_view(self, w as int, b as int);
                            Self::lemma_alloc_loop_step_inv(
                                &old_self, &loop_old_self, self, start as int, alloc_offset as int, idx as int);
                        }

                        alloc_offset += 1;
                    }
                    // Verus note: compound assignment on struct fields not supported.
                    self.usage = self.usage + size;
                    self.next_free = start + size;

                    proof {
                        old_self.lemma_alloc_range_establishes_inv(self, start as int, size as int);
                    }

                    return Ok(start);
                }
                // !free: start was advanced past the blocked position.
                proof {
                    assert(start > start_before_inner);
                }
            }
        }

        // No free range found anywhere in the bitmap.
        proof {
            assert(done);
            self.lemma_no_range_found_frame(&old_self, size as int);
            assert(!old(self).exists_contiguous_free_range(size as int));
        }
        let reason: &str = "bitmap is full";
        Err(Error::new(ErrorCode::OutOfMemory, reason))
    }

    ///
    /// # Description
    ///
    /// Sets a bit at a given index in the bitmap.
    ///
    /// # Parameters
    ///
    /// - `index`: Index of the bit to set.
    ///
    /// # Returns
    ///
    /// Upon success, `Ok(())` is returned. Upon failure, an error is returned instead.
    ///
    pub fn set(&mut self, index: usize) -> (result: Result<(), Error>)
        requires
            old(self).inv(),
        ensures
            self.inv(),
            result is Ok ==> {
                &&& (index as int) < self@.number_of_bits()
                &&& self.is_bit_set(index as int)
                &&& !old(self).is_bit_set(index as int)
                &&& self@.number_of_bits() == old(self)@.number_of_bits()
                // Frame.
                &&& forall|i: int| 0 <= i < self@.number_of_bits() && i != (index as int) ==>
                    self.is_bit_set(i) == old(self).is_bit_set(i)
                // Set-based frame.
                &&& self@.set_bits =~= old(self)@.set_bits.insert(index as int)
                &&& self@.usage() == old(self)@.usage() + 1
            },
            result is Err ==> *self == *old(self),
            ((index as int) < old(self)@.number_of_bits() && !old(self).is_bit_set(index as int))
                ==> result is Ok,
    {
        // Check if the bit is already set.
        if self.test(index)? {
            let reason: &str = "bit is already set";
            return Err(Error::new(ErrorCode::ResourceBusy, reason));
        }

        let (word, bit): (usize, usize) = self.index(index)?;
        let ghost old_self = *self;

        // At this point, we know:
        // - old_self.inv() holds
        // - !old_self.is_bit_set(index as int) (the bit is not set)
        proof {
            assert(!old_self@.set_bits.contains(index as int));
        }

        self.bits.set(word, self.bits[word] | (1 << bit));

        proof {
            old_self.lemma_set_bit_preserves_inv(self, word as int, bit as int, index as int);
        }

        self.usage = self.usage + 1;

        proof {
            assert(self.usage as int == self@.usage());
        }

        Ok(())
    }

    ///
    /// # Description
    ///
    /// Clears a bit at a given index in the bitmap.
    ///
    /// # Parameters
    ///
    /// - `index`: Index of the bit to clear.
    ///
    /// # Returns
    ///
    /// Upon success, `Ok(())` is returned. Upon failure, an error is returned instead.
    ///
    pub fn clear(&mut self, index: usize) -> (result: Result<(), Error>)
        requires
            old(self).inv(),
            (index as int) < old(self)@.number_of_bits(),
            old(self).is_bit_set(index as int),
        ensures
            self.inv(),
            result is Ok ==> {
                &&& (index as int) < self@.number_of_bits()
                &&& !self.is_bit_set(index as int)
                &&& self@.number_of_bits() == old(self)@.number_of_bits()
                // Frame.
                &&& forall|i: int| 0 <= i < self@.number_of_bits() && i != (index as int) ==>
                    self.is_bit_set(i) == old(self).is_bit_set(i)
                // Set-based frame.
                &&& self@.set_bits =~= old(self)@.set_bits.remove(index as int)
                &&& self@.usage() == old(self)@.usage() - 1
            },
            // Liveness: given preconditions, always succeeds.
            result is Ok,
    {
        // TODO: remove this runtime check once all callers are verified.
        // Check if the bit is already cleared.
        if !self.test(index)? {
            let reason: &str = "bit is already cleared";
            return Err(Error::new(ErrorCode::BadAddress, reason));
        }

        let (word, bit): (usize, usize) = self.index(index)?;
        let ghost old_self = *self;

        // At this point, we know:
        // - old_self.inv() holds
        // - old_self.is_bit_set(index as int) (the bit is set)
        proof {
            assert(old_self@.set_bits.contains(index as int));
        }

        self.bits.set(word, self.bits[word] & !(1 << bit));

        proof {
            old_self.lemma_clear_bit_preserves_inv(self, word as int, bit as int, index as int);
        }

        self.usage = self.usage - 1;
        if index < self.next_free {
            self.next_free = index;
        }

        proof {
            assert(self.usage as int == self@.usage());
        }

        Ok(())
    }

    ///
    /// # Description
    ///
    /// Tests a bit at a given index in the bitmap.
    ///
    /// # Parameters
    ///
    /// - `index`: Index of the bit to test.
    ///
    /// # Returns
    ///
    /// Upon success, `Ok(true)` is returned if the bit is set, `Ok(false)` is returned otherwise.
    /// Upon failure, an error is returned instead.
    ///
    pub fn test(&self, index: usize) -> (result: Result<bool, Error>)
        requires
            self.inv(),
        ensures
            result is Ok ==> {
                &&& (index as int) < self@.number_of_bits()
                &&& result->Ok_0 == self.is_bit_set(index as int)
            },
            result is Err ==> index as int >= self@.number_of_bits(),
            (index as int) < self@.number_of_bits() ==> result is Ok,
    {
        let (word, bit): (usize, usize) = self.index(index)?;
        Ok((self.bits[word] & (1 << bit)) != 0)
    }

    ///
    /// # Description
    ///
    /// Returns the `(word, bit)` pair of a index.
    ///
    /// # Parameters
    ///
    /// - `index`: Index of the bit.
    ///
    /// # Returns
    ///
    /// Upon success, the `(word, bit)` pair of the index is returned. Upon
    /// failure, an error is returned instead.
    ///
    fn index(&self, index: usize) -> (result: Result<(usize, usize), Error>)
        requires
            self.inv(),
        ensures
            result is Ok ==> {
                &&& index < self.number_of_bits
                &&& result->Ok_0.0 < self.bits@.len()
                &&& result->Ok_0.1 < u8::BITS as usize
                &&& result->Ok_0.0 as int == index as int / (u8::BITS as int)
                &&& result->Ok_0.1 as int == index as int % (u8::BITS as int)
            },
            result is Err ==> index >= self.number_of_bits,
            index < self.number_of_bits ==> result is Ok,
    {
        // Check if the index is out of bounds.
        if index >= self.bits.len() * u8::BITS as usize {
            let reason: &str = "index out of bounds";
            return Err(Error::new(ErrorCode::InvalidArgument, reason));
        }

        Ok(self.index_unchecked(index))
    }

    ///
    /// # Description
    ///
    /// Returns the `(word, bit)` pair of a index without checking bounds.
    ///
    /// # Parameters
    ///
    /// - `index`: Index of the bit.
    ///
    /// # Returns
    ///
    /// The `(word, bit)` pair of the index.
    ///
    fn index_unchecked(&self, index: usize) -> (result: (usize, usize))
        requires
            index < self.bits@.len() * u8::BITS as usize,
        ensures
            result.0 < self.bits@.len(),
            result.1 < u8::BITS as usize,
            result.0 as int == index as int / (u8::BITS as int),
            result.1 as int == index as int % (u8::BITS as int),
    {
        let word: usize = index / u8::BITS as usize;
        let bit: usize = index % u8::BITS as usize;
        (word, bit)
    }
}

} // verus!

// Deref implementation for test support (external to verification).
#[cfg(test)]
#[cfg_attr(verus_keep_ghost, verifier::external)]
impl ::core::ops::Deref for Bitmap {
    type Target = RawArray<u8>;

    fn deref(&self) -> &Self::Target {
        &self.bits
    }
}
