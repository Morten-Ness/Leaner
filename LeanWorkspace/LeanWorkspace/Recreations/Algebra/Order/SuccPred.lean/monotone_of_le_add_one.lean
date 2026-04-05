import Mathlib

variable {α : Type*} {x y : α}

variable {α β : Type*} [PartialOrder α] [Preorder β]

variable [Add α] [One α] [SuccAddOrder α] [IsSuccArchimedean α] {s : Set α} {f : α → β}

theorem monotone_of_le_add_one : (∀ a, ¬ IsMax a → f a ≤ f (a + 1)) → Monotone f := by
  simpa [Order.succ_eq_add_one] using monotone_of_le_succ (f := f)

