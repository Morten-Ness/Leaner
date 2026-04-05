import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

variable [Fintype n] [Fintype m]

variable [StarOrderedRing R']

omit [Fintype m] in variable [Finite m] in
theorem fromBlocks₂₂ [DecidableEq n] (A : Matrix m m R')
    (B : Matrix m n R') {D : Matrix n n R'} (hD : D.PosDef) [Invertible D] :
    (fromBlocks A B Bᴴ D).PosSemidef ↔ (A - B * D⁻¹ * Bᴴ).PosSemidef := by
  rw [← Matrix.posSemidef_submatrix_equiv (Equiv.sumComm n m), Equiv.sumComm_apply,
    fromBlocks_submatrix_sum_swap_sum_swap]
  convert Matrix.PosDef.fromBlocks₁₁ Bᴴ A hD <;> simp

