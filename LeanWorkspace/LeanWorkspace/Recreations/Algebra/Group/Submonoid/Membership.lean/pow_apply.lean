import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem pow_apply (n : M) (m : ℕ) : Submonoid.pow n m = ⟨n ^ m, m, rfl⟩ := rfl

