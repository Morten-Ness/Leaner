import Mathlib

variable {α : Type*} {x y : α}

variable {α β : Type*} [PartialOrder α] [Preorder β]

variable [Add α] [One α] [SuccAddOrder α] [IsSuccArchimedean α] {s : Set α} {f : α → β}

theorem antitoneOn_of_add_one_le (hs : s.OrdConnected) :
    (∀ a, ¬ IsMax a → a ∈ s → a + 1 ∈ s → f (a + 1) ≤ f a) → AntitoneOn f s := by
  simpa [Order.succ_eq_add_one] using antitoneOn_of_succ_le hs (f := f)

