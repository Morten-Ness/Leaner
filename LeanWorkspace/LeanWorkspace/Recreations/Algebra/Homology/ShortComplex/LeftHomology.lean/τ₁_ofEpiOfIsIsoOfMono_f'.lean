import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

set_option backward.isDefEq.respectTransparency false in
theorem τ₁_ofEpiOfIsIsoOfMono_f' (φ : S₁ ⟶ S₂) (h : CategoryTheory.ShortComplex.LeftHomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : φ.τ₁ ≫ (CategoryTheory.ShortComplex.LeftHomologyData.ofEpiOfIsIsoOfMono φ h).f' = h.f' := by
  rw [← cancel_mono (CategoryTheory.ShortComplex.LeftHomologyData.ofEpiOfIsIsoOfMono φ h).i, assoc, f'_i,
    ofEpiOfIsIsoOfMono_i, f'_i_assoc, φ.comm₁₂]

