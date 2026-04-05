import Mathlib

variable {m n R A : Type*} [CommRing R] [Fintype m] [Fintype n] [CommRing A] [IsDomain A]
  {M : Matrix m n R}

variable [DecidableEq m] {M : Matrix m m A}

theorem nondegenerate_of_det_ne_zero (hM : M.det ≠ 0) : Nondegenerate M := by
  refine Matrix.nondegenerate_def.mpr ⟨fun v h ↦ ?_, fun w h ↦ ?_⟩
  · ext i
    specialize h (M.cramer (Pi.single i 1))
    simp_all
  · ext i
    contrapose! h
    use Pi.single i 1 ᵥ* M.adjugate
    rw [dotProduct_mulVec, vecMul_vecMul, adjugate_mul]
    simp_all [dotProduct, smul_apply, smul_eq_mul, Matrix.one_apply]

