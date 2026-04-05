import Mathlib

variable {M : Type*}

variable [Monoid M] {p q a b : M}

theorem of_irreducible_mul : Irreducible (a * b) → IsUnit a ∨ IsUnit b | ⟨_, h⟩ => h rfl
