import Mathlib

variable {α : Type*} {x y : α}

variable {α β : Type*} [PartialOrder α] [Preorder β]

variable [Add α] [One α] [SuccAddOrder α] [IsSuccArchimedean α] {s : Set α} {f : α → β}

theorem strictAnti_of_add_one_lt : (∀ a, ¬ IsMax a → f (a + 1) < f a) → StrictAnti f := by
  simpa [Order.succ_eq_add_one] using strictAnti_of_succ_lt (f := f)

