import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable [IsDomain R₂] [Module.Free R₂ M₂] [Module.Finite R₂ M₂] {B : BilinForm R₂ M₂}

theorem Nondegenerate.ofSeparatingLeft (hB : SeparatingLeft B) : B.Nondegenerate := by
  obtain ⟨ι, b⟩ := Module.Free.exists_basis R₂ M₂
  have : Finite ι := Module.Finite.finite_basis b
  have : Fintype ι := Fintype.ofFinite ι
  have : DecidableEq ι := Classical.decEq ι
  rwa [← LinearMap.BilinForm.nondegenerate_toMatrix_iff b, Matrix.nondegenerate_iff_det_ne_zero,
    ← Matrix.separatingLeft_iff_det_ne_zero, LinearMap.BilinForm.separatingLeft_toMatrix_iff]

