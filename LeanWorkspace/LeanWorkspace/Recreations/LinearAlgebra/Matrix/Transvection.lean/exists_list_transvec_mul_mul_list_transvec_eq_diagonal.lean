import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R} {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜)

variable {n p} [Fintype n] [Fintype p]

theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal (M : Matrix n n 𝕜) :
    ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
      (L.map Matrix.TransvectionStruct.toMatrix).prod * M * (L'.map Matrix.TransvectionStruct.toMatrix).prod = diagonal D := by
  have e : n ≃ Fin (Fintype.card n) := Fintype.equivOfCardEq (by simp)
  apply Matrix.Pivot.reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal M e
  apply Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux

