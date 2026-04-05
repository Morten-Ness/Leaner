import Mathlib

variable {α G M : Type*}

theorem Finset.prod_fin_Icc_eq_prod_nat_Icc [CommMonoid α] {n : ℕ} (a b : Fin n) (f : Fin n → α) :
    ∏ i ∈ Icc a b, f i = ∏ i ∈ Icc (a : ℕ) b, if h : i < n then f ⟨i, h⟩ else 1 := by
  rw [← prod_ite_mem_eq, prod_fin_eq_prod_range]
  apply prod_congr_of_eq_on_inter <;> grind

