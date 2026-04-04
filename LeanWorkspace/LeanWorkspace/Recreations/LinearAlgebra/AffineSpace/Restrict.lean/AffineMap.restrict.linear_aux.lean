import Mathlib

variable {k V₁ P₁ V₂ P₂ : Type*} [Ring k] [AddCommGroup V₁] [AddCommGroup V₂] [Module k V₁]
  [Module k V₂] [AddTorsor V₁ P₁] [AddTorsor V₂ P₂]

theorem AffineMap.restrict.linear_aux {φ : P₁ →ᵃ[k] P₂} {E : AffineSubspace k P₁}
    {F : AffineSubspace k P₂} (hEF : E.map φ ≤ F) : E.direction ≤ F.direction.comap φ.linear := by
  rw [← Submodule.map_le_iff_le_comap, ← AffineSubspace.map_direction]
  exact AffineSubspace.direction_le hEF

