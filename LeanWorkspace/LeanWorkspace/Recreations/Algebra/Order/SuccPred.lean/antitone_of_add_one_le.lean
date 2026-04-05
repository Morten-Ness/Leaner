import Mathlib

variable {α : Type*} {x y : α}

variable {α β : Type*} [PartialOrder α] [Preorder β]

variable [Add α] [One α] [SuccAddOrder α] [IsSuccArchimedean α] {s : Set α} {f : α → β}

theorem antitone_of_add_one_le : (∀ a, ¬ IsMax a → f (a + 1) ≤ f a) → Antitone f := by
  simpa [Order.succ_eq_add_one] using antitone_of_succ_le (f := f)

