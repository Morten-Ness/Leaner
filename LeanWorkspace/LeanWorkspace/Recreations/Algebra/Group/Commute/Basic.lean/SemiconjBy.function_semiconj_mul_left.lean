import Mathlib

variable {G : Type*}

variable [Semigroup G] {a b c : G}

theorem SemiconjBy.function_semiconj_mul_left (h : SemiconjBy a b c) :
    Semiconj (a * ·) (b * ·) (c * ·) := fun j ↦ by simp only [← mul_assoc, h.eq]

