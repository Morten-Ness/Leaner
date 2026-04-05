import Mathlib

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*}

variable [Fintype n]

theorem Matrix.mulVec_injective_iff {M : Matrix m n R} :
    Function.Injective M.mulVec ↔ LinearIndependent R M.col := by
  change Function.Injective (fun x ↦ _) ↔ _
  simp_rw [← M.vecMul_transpose, vecMul_injective_iff, row_transpose]

