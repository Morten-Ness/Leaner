import Mathlib

variable {R A : Type*}

theorem CharP.dvd_of_ringHom [NonAssocSemiring R] [NonAssocSemiring A]
    (f : R →+* A) (p q : ℕ) [CharP R p] [CharP A q] : q ∣ p := by
  refine (CharP.cast_eq_zero_iff A q p).mp ?_
  rw [← map_natCast f p, CharP.cast_eq_zero, map_zero]

