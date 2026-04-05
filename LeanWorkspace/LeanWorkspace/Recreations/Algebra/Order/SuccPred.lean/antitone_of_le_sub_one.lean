import Mathlib

variable {α : Type*} {x y : α}

variable {α β : Type*} [PartialOrder α] [Preorder β]

variable [Sub α] [One α] [PredSubOrder α] [IsPredArchimedean α] {s : Set α} {f : α → β}

theorem antitone_of_le_sub_one : (∀ a, ¬ IsMin a → f a ≤ f (a - 1)) → Antitone f := by
  simpa [Order.pred_eq_sub_one] using antitone_of_le_pred (f := f)

