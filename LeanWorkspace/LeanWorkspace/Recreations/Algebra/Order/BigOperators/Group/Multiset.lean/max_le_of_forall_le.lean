import Mathlib

variable {ι α β : Type*}

theorem max_le_of_forall_le {α : Type*} [LinearOrder α] [OrderBot α] (l : Multiset α)
    (n : α) (h : ∀ x ∈ l, x ≤ n) : l.fold max ⊥ ≤ n := by
  induction l using Quotient.inductionOn
  simpa using List.max_le_of_forall_le _ _ h

