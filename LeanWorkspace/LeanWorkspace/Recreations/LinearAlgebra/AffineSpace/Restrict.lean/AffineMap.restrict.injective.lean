import Mathlib

variable {k V₁ P₁ V₂ P₂ : Type*} [Ring k] [AddCommGroup V₁] [AddCommGroup V₂] [Module k V₁]
  [Module k V₂] [AddTorsor V₁ P₁] [AddTorsor V₂ P₂]

theorem AffineMap.restrict.injective {φ : P₁ →ᵃ[k] P₂} (hφ : Function.Injective φ)
    {E : AffineSubspace k P₁} {F : AffineSubspace k P₂} [Nonempty E] [Nonempty F]
    (hEF : E.map φ ≤ F) : Function.Injective (AffineMap.restrict φ hEF) := by
  intro x y h
  simp only [Subtype.ext_iff, AffineMap.restrict.coe_apply] at h ⊢
  exact hφ h

