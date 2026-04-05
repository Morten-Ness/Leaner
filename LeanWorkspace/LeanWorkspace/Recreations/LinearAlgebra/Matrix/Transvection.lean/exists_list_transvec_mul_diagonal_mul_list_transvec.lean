import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R} {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜)

variable {n p} [Fintype n] [Fintype p]

theorem exists_list_transvec_mul_diagonal_mul_list_transvec (M : Matrix n n 𝕜) :
    ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
      M = (L.map Matrix.TransvectionStruct.toMatrix).prod * diagonal D * (L'.map Matrix.TransvectionStruct.toMatrix).prod := by
  rcases Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal M with ⟨L, L', D, h⟩
  refine ⟨L.reverse.map TransvectionStruct.inv, L'.reverse.map TransvectionStruct.inv, D, ?_⟩
  suffices
    M =
      (L.reverse.map (Matrix.TransvectionStruct.toMatrix ∘ TransvectionStruct.inv)).prod * (L.map Matrix.TransvectionStruct.toMatrix).prod * M *
        ((L'.map Matrix.TransvectionStruct.toMatrix).prod * (L'.reverse.map (Matrix.TransvectionStruct.toMatrix ∘ TransvectionStruct.inv)).prod)
    by simpa [← h, Matrix.mul_assoc]
  rw [Matrix.TransvectionStruct.reverse_inv_prod_mul_prod, Matrix.TransvectionStruct.prod_mul_reverse_inv_prod, Matrix.one_mul, Matrix.mul_one]

