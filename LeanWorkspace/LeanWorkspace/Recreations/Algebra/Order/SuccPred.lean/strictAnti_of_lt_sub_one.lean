import Mathlib

variable {α : Type*} {x y : α}

variable {α β : Type*} [PartialOrder α] [Preorder β]

variable [Sub α] [One α] [PredSubOrder α] [IsPredArchimedean α] {s : Set α} {f : α → β}

theorem strictAnti_of_lt_sub_one : (∀ a, ¬ IsMin a → f a < f (a - 1)) → StrictAnti f := by
  simpa [Order.pred_eq_sub_one] using strictAnti_of_lt_pred (f := f)

