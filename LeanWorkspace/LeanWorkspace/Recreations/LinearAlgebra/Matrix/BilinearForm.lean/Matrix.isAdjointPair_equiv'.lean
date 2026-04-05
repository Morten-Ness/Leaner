import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n : Type*} [Fintype n]

variable (b : Basis n R₂ M₂)

variable (J J₃ A A' : Matrix n n R₂)

theorem Matrix.isAdjointPair_equiv' [DecidableEq n] (P : Matrix n n R₂) (h : IsUnit P) :
    (Pᵀ * J * P).IsAdjointPair (Pᵀ * J * P) A A' ↔
      J.IsAdjointPair J (P * A * P⁻¹) (P * A' * P⁻¹) := Matrix.isAdjointPair_equiv _ _ _ _ h

