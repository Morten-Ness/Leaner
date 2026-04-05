import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable (h : RightHomologyData S) {A : C}
  (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [HasRightHomology S]

theorem opcyclesMap_comp_descOpcycles (φ : S₁ ⟶ S) [S₁.HasRightHomology] :
    CategoryTheory.ShortComplex.opcyclesMap φ ≫ S.descOpcycles k hk =
      S₁.descOpcycles (φ.τ₂ ≫ k) (by rw [← φ.comm₁₂_assoc, hk, comp_zero]) := by
  simp only [← cancel_epi (S₁.pOpcycles), p_opcyclesMap_assoc, CategoryTheory.ShortComplex.p_descOpcycles]

