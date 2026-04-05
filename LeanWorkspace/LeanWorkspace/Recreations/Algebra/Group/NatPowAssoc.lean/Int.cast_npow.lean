import Mathlib

variable {M : Type*}

variable [Monoid M]

theorem Int.cast_npow (R : Type*) [NonAssocRing R] [Pow R ℕ] [NatPowAssoc R]
    (n : ℤ) : ∀ (m : ℕ), @Int.cast R NonAssocRing.toIntCast (n ^ m) = (n : R) ^ m
  | 0 => by
    rw [pow_zero, npow_zero, Int.cast_one]
  | m + 1 => by
    rw [npow_add, npow_one, Int.cast_mul, Int.cast_npow R n m, npow_add, npow_one]
