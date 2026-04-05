import Mathlib

variable {α : Type*} {x y : α}

variable {α β : Type*} [PartialOrder α] [Preorder β]

variable [Add α] [One α] [SuccAddOrder α] [IsSuccArchimedean α] {s : Set α} {f : α → β}

theorem strictMono_of_lt_add_one : (∀ a, ¬ IsMax a → f a < f (a + 1)) → StrictMono f := by
  simpa [Order.succ_eq_add_one] using strictMono_of_lt_succ (f := f)

