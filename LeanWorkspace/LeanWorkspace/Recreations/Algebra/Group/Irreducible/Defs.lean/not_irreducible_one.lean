import Mathlib

variable {M : Type*}

variable [Monoid M] {p q a b : M}

theorem not_irreducible_one : ¬Irreducible (1 : M) := by simp [irreducible_iff]

