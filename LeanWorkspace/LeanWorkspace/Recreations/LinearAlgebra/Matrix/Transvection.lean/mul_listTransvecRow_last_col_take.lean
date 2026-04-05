import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R} {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜)

theorem mul_listTransvecRow_last_col_take (i : Fin r ⊕ Unit) {k : ℕ} (hk : k ≤ r) :
    (M * ((Matrix.Pivot.listTransvecRow M).take k).prod) i (inr unit) = M i (inr unit) := by
  induction k with
  | zero => simp only [Matrix.mul_one, List.prod_nil, List.take, Matrix.mul_one]
  | succ k IH =>
    have hkr : k < r := hk
    let k' : Fin r := ⟨k, hkr⟩
    have :
      (Matrix.Pivot.listTransvecRow M)[k]? =
        ↑(Matrix.transvection (inr Unit.unit) (inl k')
            (-M (inr Unit.unit) (inl k') / M (inr Unit.unit) (inr Unit.unit))) := by
      simp only [k', Matrix.Pivot.listTransvecRow, hkr, dif_pos, List.getElem?_ofFn]
    simp only [List.take_add_one, ← Matrix.mul_assoc, this, List.prod_append, Matrix.mul_one,
      List.prod_cons, List.prod_nil, Option.toList_some]
    rw [Matrix.mul_transvection_apply_of_ne, IH hkr.le]
    simp only [Ne, not_false_iff, reduceCtorEq]

