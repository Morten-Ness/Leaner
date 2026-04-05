import Mathlib

variable {R S : Type*}

variable {R : Type*} [NonUnitalNonAssocRing R] {r : R}

theorem isCancelMulZero_iff_noZeroDivisors : IsCancelMulZero R ↔ NoZeroDivisors R := noZeroDivisors_tfae.out 3 0

