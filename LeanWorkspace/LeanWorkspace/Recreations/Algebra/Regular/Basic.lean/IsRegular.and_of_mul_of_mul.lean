import Mathlib

variable {R : Type*}

variable [Semigroup R] {a b : R}

theorem IsRegular.and_of_mul_of_mul (ab : IsRegular (a * b)) (ba : IsRegular (b * a)) :
    IsRegular a ∧ IsRegular b := isRegular_mul_and_mul_iff.mp ⟨ab, ba⟩

