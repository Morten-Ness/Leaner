import Mathlib

variable {α : Type u}

variable [LinearOrder α] [DenselyOrdered α] [Monoid α] [ExistsMulOfLE α]
  [MulLeftReflectLT α] {a b : α}

theorem le_iff_forall_one_lt_le_mul [MulLeftStrictMono α] :
    a ≤ b ↔ ∀ ε, 1 < ε → a ≤ b * ε := ⟨fun h _ hε ↦ lt_mul_of_le_of_one_lt h hε |>.le, le_of_forall_one_lt_le_mul⟩

