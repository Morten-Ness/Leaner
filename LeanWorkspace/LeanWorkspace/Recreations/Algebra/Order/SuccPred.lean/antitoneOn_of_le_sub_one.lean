import Mathlib

variable {α : Type*} {x y : α}

variable {α β : Type*} [PartialOrder α] [Preorder β]

variable [Sub α] [One α] [PredSubOrder α] [IsPredArchimedean α] {s : Set α} {f : α → β}

theorem antitoneOn_of_le_sub_one (hs : s.OrdConnected) :
    (∀ a, ¬ IsMin a → a ∈ s → a - 1 ∈ s → f a ≤ f (a - 1)) → AntitoneOn f s := by
  simpa [Order.pred_eq_sub_one] using antitoneOn_of_le_pred hs (f := f)

