import Mathlib

variable {R A : Type*}

theorem charP_of_injective_ringHom [NonAssocSemiring R] [NonAssocSemiring A]
    {f : R →+* A} (h : Function.Injective f) (p : ℕ) [CharP R p] : CharP A p where
  cast_eq_zero_iff x := by
    rw [← CharP.cast_eq_zero_iff R p x, ← map_natCast f x, map_eq_zero_iff f h]

