import Mathlib

variable {α G M : Type*}

theorem Fin.prod_Icc_div [CommGroup M] {n : ℕ} {a b : Fin n} (hab : a ≤ b)
    (f : Fin (n + 1) → M) :
    ∏ i ∈ Icc a b, (f i.succ / f i.castSucc) = f b.succ / f a.castSucc := by
  rw [prod_fin_Icc_eq_prod_nat_Icc]
  convert Finset.prod_Icc_div (Fin.le_def.1 hab) (fun i ↦ if hi : i < n + 1 then f ⟨i, hi⟩ else 1)
  · simp_all
    grind
  · grind
  · simp only [Order.lt_add_one_iff, is_le', ↓reduceDIte]
    rfl

