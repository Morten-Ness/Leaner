import Mathlib

variable {α : Type u}

variable [LinearOrder α] [DenselyOrdered α] [Monoid α] [ExistsMulOfLE α]
  [MulLeftReflectLT α] {a b : α}

theorem le_of_forall_one_lt_lt_mul' (h : ∀ ε : α, 1 < ε → a < b * ε) : a ≤ b := le_of_forall_one_lt_le_mul fun ε hε => (h ε hε).le

