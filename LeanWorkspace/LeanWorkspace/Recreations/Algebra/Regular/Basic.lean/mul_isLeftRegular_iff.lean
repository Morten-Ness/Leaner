import Mathlib

variable {R : Type*}

variable [Semigroup R] {a b : R}

theorem mul_isLeftRegular_iff (b : R) (ha : IsLeftRegular a) :
    IsLeftRegular (a * b) ↔ IsLeftRegular b := ⟨fun ab => IsLeftRegular.of_mul ab, fun ab => IsLeftRegular.mul ha ab⟩

