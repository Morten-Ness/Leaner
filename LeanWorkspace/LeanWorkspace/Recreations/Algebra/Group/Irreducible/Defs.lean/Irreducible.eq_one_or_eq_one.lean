import Mathlib

variable {M : Type*}

variable [Monoid M] {p q a b : M}

theorem Irreducible.eq_one_or_eq_one [Subsingleton Mˣ] (hab : Irreducible (a * b)) :
    a = 1 ∨ b = 1 := by simpa using hab.isUnit_or_isUnit rfl

