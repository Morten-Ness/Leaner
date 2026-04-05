import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

variable [NoZeroDivisors R] [Nontrivial R]

theorem torsion_int {G} [AddCommGroup G] :
    (torsion ℤ G).toAddSubgroup = AddCommGroup.torsion G := by
  ext x
  refine ((isOfFinAddOrder_iff_zsmul_eq_zero (x := x)).trans ?_).symm
  simp [mem_nonZeroDivisors_iff_ne_zero]

