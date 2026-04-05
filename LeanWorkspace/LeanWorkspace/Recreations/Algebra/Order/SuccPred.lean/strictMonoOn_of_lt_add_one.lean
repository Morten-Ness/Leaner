import Mathlib

variable {α : Type*} {x y : α}

variable {α β : Type*} [PartialOrder α] [Preorder β]

variable [Add α] [One α] [SuccAddOrder α] [IsSuccArchimedean α] {s : Set α} {f : α → β}

theorem strictMonoOn_of_lt_add_one (hs : s.OrdConnected) :
    (∀ a, ¬ IsMax a → a ∈ s → a + 1 ∈ s → f a < f (a + 1)) → StrictMonoOn f s := by
  simpa [Order.succ_eq_add_one] using strictMonoOn_of_lt_succ hs (f := f)

