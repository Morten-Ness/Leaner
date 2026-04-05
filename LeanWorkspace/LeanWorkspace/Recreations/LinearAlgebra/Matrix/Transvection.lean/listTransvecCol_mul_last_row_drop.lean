import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R} {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜)

theorem listTransvecCol_mul_last_row_drop (i : Fin r ⊕ Unit) {k : ℕ} (hk : k ≤ r) :
    (((Matrix.Pivot.listTransvecCol M).drop k).prod * M) (inr unit) i = M (inr unit) i := by
  induction hk using Nat.decreasingInduction with
  | of_succ n hn IH =>
    have hn' : n < (Matrix.Pivot.listTransvecCol M).length := by simpa [Matrix.Pivot.listTransvecCol] using hn
    rw [List.drop_eq_getElem_cons hn']
    simpa [Matrix.Pivot.listTransvecCol, Matrix.mul_assoc]
  | self =>
    simp only [Matrix.Pivot.length_listTransvecCol, le_refl, List.drop_eq_nil_of_le, List.prod_nil,
      Matrix.one_mul]

