import Mathlib

variable {α : Type*} {x y : α}

variable {α β : Type*} [PartialOrder α] [Preorder β]

variable [Add α] [One α] [SuccAddOrder α] [IsSuccArchimedean α] {s : Set α} {f : α → β}

theorem monotoneOn_of_le_add_one (hs : s.OrdConnected) :
    (∀ a, ¬ IsMax a → a ∈ s → a + 1 ∈ s → f a ≤ f (a + 1)) → MonotoneOn f s := by
  simpa [Order.succ_eq_add_one] using monotoneOn_of_le_succ hs (f := f)

