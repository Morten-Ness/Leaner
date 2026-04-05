import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

variable [IsStrictOrderedRing K]

variable [FloorRing K]

variable [Fintype ι]

theorem repr_floor_apply (m : E) (i : ι) : b.repr (ZSpan.floor b m) i = ⌊b.repr m i⌋ := by
  classical simp only [ZSpan.floor, ← Int.cast_smul_eq_zsmul K, b.repr.map_smul, Finsupp.single_apply,
    Finset.sum_apply', Module.Basis.repr_self, Finsupp.smul_single', mul_one, Finset.sum_ite_eq', coe_sum,
    Finset.mem_univ, if_true, coe_smul_of_tower, Module.Basis.restrictScalars_apply, map_sum]

