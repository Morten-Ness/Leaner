import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

set_option backward.isDefEq.respectTransparency false in
theorem ofEpiOfIsIsoOfMono'_f' (φ : S₁ ⟶ S₂) (h : CategoryTheory.ShortComplex.LeftHomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : (CategoryTheory.ShortComplex.LeftHomologyData.ofEpiOfIsIsoOfMono' φ h).f' = φ.τ₁ ≫ h.f' := by
  rw [← cancel_mono (CategoryTheory.ShortComplex.LeftHomologyData.ofEpiOfIsIsoOfMono' φ h).i, f'_i, ofEpiOfIsIsoOfMono'_i,
    assoc, f'_i_assoc, φ.comm₁₂_assoc, IsIso.hom_inv_id, comp_id]

