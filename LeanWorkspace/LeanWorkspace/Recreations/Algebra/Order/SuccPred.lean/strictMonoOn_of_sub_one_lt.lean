import Mathlib

variable {α : Type*} {x y : α}

variable {α β : Type*} [PartialOrder α] [Preorder β]

variable [Sub α] [One α] [PredSubOrder α] [IsPredArchimedean α] {s : Set α} {f : α → β}

theorem strictMonoOn_of_sub_one_lt (hs : s.OrdConnected) :
    (∀ a, ¬ IsMin a → a ∈ s → a - 1 ∈ s → f (a - 1) < f a) → StrictMonoOn f s := by
  simpa [Order.pred_eq_sub_one] using strictMonoOn_of_pred_lt hs (f := f)

