import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

variable [IsStrictOrderedRing K]

variable [FloorRing K]

variable [Fintype ι]

theorem norm_fract_le [HasSolidNorm K] (m : E) : ‖ZSpan.fract b m‖ ≤ ∑ i, ‖b i‖ := by
  classical
  calc
    ‖ZSpan.fract b m‖ = ‖∑ i, b.repr (ZSpan.fract b m) i • b i‖ := by rw [b.sum_repr]
    _ = ‖∑ i, Int.fract (b.repr m i) • b i‖ := by simp_rw [ZSpan.repr_fract_apply]
    _ ≤ ∑ i, ‖Int.fract (b.repr m i) • b i‖ := norm_sum_le _ _
    _ = ∑ i, ‖Int.fract (b.repr m i)‖ * ‖b i‖ := by simp_rw [norm_smul]
    _ ≤ ∑ i, ‖b i‖ := Finset.sum_le_sum fun i _ => ?_
  suffices ‖Int.fract ((b.repr m) i)‖ ≤ 1 by
    convert mul_le_mul_of_nonneg_right this (norm_nonneg _ : 0 ≤ ‖b i‖)
    exact (one_mul _).symm
  rw [(norm_one.symm : 1 = ‖(1 : K)‖)]
  apply norm_le_norm_of_abs_le_abs
  rw [abs_one, Int.abs_fract]
  exact le_of_lt (Int.fract_lt_one _)

