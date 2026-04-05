import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {A : Type*} [CommRing A] [IsDomain A] [Module A M₂] (B₃ : BilinForm A M₂)

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

theorem Nondegenerate.toMatrix' {B : LinearMap.BilinForm R₂ (ι → R₂)} (h : B.Nondegenerate) :
    B.toMatrix'.Nondegenerate := h.toMatrix₂'

