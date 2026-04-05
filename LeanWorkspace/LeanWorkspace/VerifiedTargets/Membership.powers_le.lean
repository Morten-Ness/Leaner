import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem powers_le {n : M} {P : Submonoid M} : Submonoid.powers n ≤ P ↔ n ∈ P := by simp [Submonoid.powers_eq_closure]

