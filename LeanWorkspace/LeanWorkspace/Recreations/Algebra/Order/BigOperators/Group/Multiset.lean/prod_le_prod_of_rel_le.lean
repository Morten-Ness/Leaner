import Mathlib

variable {ι α β : Type*}

variable [CommMonoid α] [Preorder α] {s t : Multiset α} {a : α}

theorem prod_le_prod_of_rel_le [MulLeftMono α] (h : s.Rel (· ≤ ·) t) : s.prod ≤ t.prod := by
  induction h with
  | zero => rfl
  | cons rh _ rt =>
    rw [prod_cons, prod_cons]
    exact mul_le_mul' rh rt

