import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β]

variable (f : F) {s t : Finset α} {a b : α}

theorem isUnit_iff_singleton_aux {α} [Group α] {s : Finset α} :
    (∃ a, s = {a} ∧ IsUnit a) ↔ ∃ a, s = {a} := by
  simp only [Group.isUnit, and_true]

