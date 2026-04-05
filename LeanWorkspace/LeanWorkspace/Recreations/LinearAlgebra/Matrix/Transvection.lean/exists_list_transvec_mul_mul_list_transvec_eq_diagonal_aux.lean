import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R} {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜)

variable {n p} [Fintype n] [Fintype p]

theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux (n : Type) [Fintype n]
    [DecidableEq n] (M : Matrix n n 𝕜) :
    ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
      (L.map Matrix.TransvectionStruct.toMatrix).prod * M * (L'.map Matrix.TransvectionStruct.toMatrix).prod = diagonal D := by
  suffices ∀ cn, Fintype.card n = cn →
      ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
      (L.map Matrix.TransvectionStruct.toMatrix).prod * M * (L'.map Matrix.TransvectionStruct.toMatrix).prod = diagonal D by exact this _ rfl
  intro cn hn
  induction cn generalizing n M with
  | zero =>
    refine ⟨List.nil, List.nil, fun _ => 1, ?_⟩
    ext i j
    rw [Fintype.card_eq_zero_iff] at hn
    exact hn.elim' i
  | succ r IH =>
    have e : n ≃ Fin r ⊕ Unit := by
      refine Fintype.equivOfCardEq ?_
      rw [hn]
      rw [@Fintype.card_sum (Fin r) Unit _ _]
      simp
    apply Matrix.Pivot.reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal M e
    apply
      Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction fun N =>
        IH (Fin r) N (by simp)

