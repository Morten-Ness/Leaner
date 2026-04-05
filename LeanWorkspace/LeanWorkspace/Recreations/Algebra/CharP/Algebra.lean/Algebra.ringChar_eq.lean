import Mathlib

variable {R A : Type*}

variable (K L : Type*) [Field K] [CommSemiring L] [Nontrivial L] [Algebra K L]

theorem Algebra.ringChar_eq : ringChar K = ringChar L := by
  rw [ringChar.eq_iff, Algebra.charP_iff K L]
  apply ringChar.charP

