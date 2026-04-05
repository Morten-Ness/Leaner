import Mathlib

variable {α : Type*} {x y : α}

variable {α β : Type*} [PartialOrder α] [Preorder β]

variable [Sub α] [One α] [PredSubOrder α] [IsPredArchimedean α] {s : Set α} {f : α → β}

theorem strictAntiOn_of_lt_sub_one (hs : s.OrdConnected) :
    (∀ a, ¬ IsMin a → a ∈ s → a - 1 ∈ s → f a < f (a - 1)) → StrictAntiOn f s := by
  simpa [Order.pred_eq_sub_one] using strictAntiOn_of_lt_pred hs (f := f)

