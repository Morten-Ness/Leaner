import Mathlib

variable {G : Type*}

variable [Semigroup G] {a b c : G}

theorem SemiconjBy.function_semiconj_mul_right_swap (h : SemiconjBy a b c) :
    Function.Semiconj (· * a) (· * c) (· * b) := fun j ↦ by simp only [mul_assoc, ← h.eq]

