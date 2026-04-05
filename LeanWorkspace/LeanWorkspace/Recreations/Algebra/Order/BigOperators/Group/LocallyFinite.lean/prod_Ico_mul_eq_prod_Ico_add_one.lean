import Mathlib

variable {α M : Type*} [CommMonoid M] {f : α → M} {a b : α}

variable [LinearOrder α]

variable [LocallyFiniteOrder α] [AddMonoidWithOne α] [SuccAddOrder α] [NoMaxOrder α]

theorem prod_Ico_mul_eq_prod_Ico_add_one (hab : a ≤ b) (f : α → M) :
    (∏ x ∈ Ico a b, f x) * f b = ∏ x ∈ Ico a (b + 1), f x := by
  rw [← Finset.insert_Ico_right_eq_Ico_add_one hab, prod_insert right_notMem_Ico, mul_comm]

