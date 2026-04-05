import Mathlib

variable {R : Type*} [Semiring R]

variable {l m n : Type*}

variable [Fintype m]

theorem range_vecMulLinear (M : Matrix m n R) :
    LinearMap.range M.vecMulLinear = span R (Set.range M.row) := by
  letI := Classical.decEq m
  simp_rw [range_eq_map, ← iSup_range_single, Submodule.map_iSup, range_eq_map, ←
    Ideal.span_singleton_one, Ideal.span, Submodule.map_span, image_image, image_singleton,
    Matrix.vecMulLinear_apply, iSup_span, range_eq_iUnion, iUnion_singleton_eq_range,
    LinearMap.single, LinearMap.coe_mk, AddHom.coe_mk, row_def]
  unfold vecMul
  simp_rw [single_dotProduct, one_mul]

