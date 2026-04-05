import Mathlib

variable {R A : Type*}

variable (K L : Type*) [Field K] [CommSemiring L] [Nontrivial L] [Algebra K L]

theorem Algebra.charP_iff (p : ℕ) : CharP K p ↔ CharP L p := (algebraMap K L).charP_iff_charP p

