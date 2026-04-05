import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {A : Type*} [CommRing A] [IsDomain A] [Module A M₂] (B₃ : BilinForm A M₂)

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

theorem nondegenerate_toBilin'_of_det_ne_zero' (M : Matrix ι ι A) (h : M.det ≠ 0) :
    M.toBilin'.Nondegenerate := LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr h

