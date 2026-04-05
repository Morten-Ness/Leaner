import Mathlib

variable {α G M : Type*}

theorem Fin.prod_Iic_div [CommGroup M] {n : ℕ} (a : Fin n) (f : Fin (n + 1) → M) :
    ∏ i ∈ Iic a, (f i.succ / f i.castSucc) = f a.succ / f 0 := by
  rw [← prod_ite_mem_eq, prod_fin_eq_prod_range]
  convert prod_range_div (fun i ↦ if hi : i < n + 1 then f ⟨i, hi⟩ else 1) (a + 1)
    using 1 with k hk
  · exact prod_congr_of_eq_on_inter (by grind) (by grind) (by simp_all; grind)
  · grind

