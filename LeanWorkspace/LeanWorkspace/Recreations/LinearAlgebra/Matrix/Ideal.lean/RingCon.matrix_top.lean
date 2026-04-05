import Mathlib

variable {R n : Type*}

variable [NonUnitalNonAssocSemiring R] [Fintype n]

theorem matrix_top : (⊤ : RingCon R).matrix n = ⊤ := eq_top_iff.2 fun _ _ _ _ _ ↦ by simp

