import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem mem_powers (n : M) : n ∈ Submonoid.powers n := ⟨1, pow_one _⟩

