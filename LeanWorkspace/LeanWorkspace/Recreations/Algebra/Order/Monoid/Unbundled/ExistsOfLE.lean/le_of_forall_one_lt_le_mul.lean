import Mathlib

variable {α : Type u}

variable [LinearOrder α] [DenselyOrdered α] [Monoid α] [ExistsMulOfLE α]
  [MulLeftReflectLT α] {a b : α}

theorem le_of_forall_one_lt_le_mul (h : ∀ ε : α, 1 < ε → a ≤ b * ε) : a ≤ b := le_of_forall_gt_imp_ge_of_dense fun x hxb => by
    obtain ⟨ε, rfl⟩ := exists_mul_of_le hxb.le
    exact h _ (one_lt_of_lt_mul_right hxb)

