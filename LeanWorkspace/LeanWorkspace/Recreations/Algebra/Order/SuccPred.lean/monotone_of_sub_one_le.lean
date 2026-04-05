import Mathlib

variable {α : Type*} {x y : α}

variable {α β : Type*} [PartialOrder α] [Preorder β]

variable [Sub α] [One α] [PredSubOrder α] [IsPredArchimedean α] {s : Set α} {f : α → β}

theorem monotone_of_sub_one_le : (∀ a, ¬ IsMin a → f (a - 1) ≤ f a) → Monotone f := by
  simpa [Order.pred_eq_sub_one] using monotone_of_pred_le (f := f)

