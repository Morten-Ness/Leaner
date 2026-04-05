import Mathlib

variable {α M : Type*} [CommMonoid M] {f : α → M} {a b : α}

variable [PartialOrder α]

variable [LocallyFiniteOrder α]

variable [AddMonoidWithOne α] [SuccAddOrder α]

theorem prod_eq_prod_Ico_succ_bot {a b : ℕ} (hab : a < b) (f : ℕ → M) :
    ∏ k ∈ Ico a b, f k = f a * ∏ k ∈ Ico (a + 1) b, f k := by
  have ha : a ∉ Ico (a + 1) b := by simp
  rw [← prod_insert ha, Finset.insert_Ico_add_one_left_eq_Ico hab]

