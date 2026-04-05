import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable [IsDomain R₂] [Module.Free R₂ M₂] [Module.Finite R₂ M₂] {B : BilinForm R₂ M₂}

theorem Nondegenerate.ofSeparatingRight (hB : B.SeparatingRight) : B.Nondegenerate := nondegenerate_flip_iff.mp <| .ofSeparatingLeft hB

