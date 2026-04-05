import Mathlib

variable {α : Type*} {x y : α}

variable {α β : Type*} [PartialOrder α] [Preorder β]

variable [Sub α] [One α] [PredSubOrder α] [IsPredArchimedean α] {s : Set α} {f : α → β}

theorem strictMono_of_sub_one_lt : (∀ a, ¬ IsMin a → f (a - 1) < f a) → StrictMono f := by
  simpa [Order.pred_eq_sub_one] using strictMono_of_pred_lt (f := f)

