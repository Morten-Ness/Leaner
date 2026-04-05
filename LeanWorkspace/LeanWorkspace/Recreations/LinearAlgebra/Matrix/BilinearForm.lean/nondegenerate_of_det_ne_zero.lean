import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {A : Type*} [CommRing A] [IsDomain A] [Module A M₂] (B₃ : BilinForm A M₂)

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

theorem nondegenerate_of_det_ne_zero (b : Module.Basis ι A M₂) (h : (LinearMap.BilinForm.toMatrix b B₃).det ≠ 0) :
    B₃.Nondegenerate := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mpr h

