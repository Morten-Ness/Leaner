import Mathlib

variable {k V₁ P₁ V₂ P₂ : Type*} [Ring k] [AddCommGroup V₁] [AddCommGroup V₂] [Module k V₁]
  [Module k V₂] [AddTorsor V₁ P₁] [AddTorsor V₂ P₂]

theorem AffineMap.restrict.bijective {E : AffineSubspace k P₁} [Nonempty E] {φ : P₁ →ᵃ[k] P₂}
    (hφ : Function.Injective φ) : Function.Bijective (φ.restrict (le_refl (E.map φ))) := ⟨AffineMap.restrict.injective hφ _, AffineMap.restrict.surjective _ rfl⟩

