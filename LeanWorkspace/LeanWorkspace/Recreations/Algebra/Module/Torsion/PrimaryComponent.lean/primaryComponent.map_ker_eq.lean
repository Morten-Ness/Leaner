import Mathlib

variable {A M M₁ M₂ : Type*} [CommRing A]

variable (I : Ideal A)

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module A M] [Module A M₁]
    [Module A M₂]

theorem primaryComponent.map_ker_eq (φ : M₁ →ₗ[A] M₂) :
    (Ideal.primaryComponent.map I φ).ker.map (Ideal.primaryComponent M₁ I).subtype =
      (Ideal.primaryComponent φ.ker I).map φ.ker.subtype := by
  aesop (add norm [map, Subtype.ext_iff, Ideal.primaryComponent_mem])

