import Mathlib

variable {M : Type*}

variable [Monoid M] {p q a b : M}

theorem Irreducible.ne_one (hp : Irreducible p) : p ≠ 1 := by rintro rfl; exact not_irreducible_one hp

