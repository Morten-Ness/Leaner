import Mathlib

variable {R : Type*}

variable [Semiring R] {p q : SkewPolynomial R}

variable {S S₁ S₂ : Type*}

variable [MulSemiringAction (Multiplicative ℕ) R]

theorem φ_def : φ = MulSemiringAction.toRingHom (Multiplicative ℕ) R (ofAdd 1) := rfl

