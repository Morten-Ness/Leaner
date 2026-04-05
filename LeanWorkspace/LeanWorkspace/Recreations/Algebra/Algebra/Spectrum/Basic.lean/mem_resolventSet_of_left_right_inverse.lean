import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem mem_resolventSet_of_left_right_inverse {r : R} {a b c : A} (h₁ : (↑ₐ r - a) * b = 1)
    (h₂ : c * (↑ₐ r - a) = 1) : r ∈ resolventSet R a := Units.isUnit ⟨↑ₐ r - a, b, h₁, by rwa [← left_inv_eq_right_inv h₂ h₁]⟩

