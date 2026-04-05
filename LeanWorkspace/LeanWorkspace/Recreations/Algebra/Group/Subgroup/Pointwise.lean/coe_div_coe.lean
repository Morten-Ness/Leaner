import Mathlib

variable {α G A S : Type*}

theorem coe_div_coe [SetLike S G] [DivisionMonoid G] [SubgroupClass S G] (H : S) :
    H / H = (H : Set G) := by simp [div_eq_mul_inv]

