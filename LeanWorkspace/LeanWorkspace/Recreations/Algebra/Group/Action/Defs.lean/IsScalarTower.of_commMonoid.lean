import Mathlib

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

theorem IsScalarTower.of_commMonoid (R₁ R : Type*)
    [Monoid R₁] [CommMonoid R] [MulAction R₁ R] [SMulCommClass R₁ R R] : IsScalarTower R₁ R R where
  smul_assoc x₁ y z := by rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← smul_comm, smul_eq_mul,
    mul_comm, ← smul_eq_mul]

