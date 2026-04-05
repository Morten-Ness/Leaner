import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [CommGroup β] [FunLike F α β] [MonoidHomClass F α β]

theorem smul_graphOn_univ (x : α × β) (f : F) :
    x • univ.graphOn f = univ.graphOn fun a ↦ x.2 / f x.1 * f a := by simp [Set.smul_graphOn]

