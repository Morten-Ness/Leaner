import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable (S) (h : LeftHomologyData S) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0)
  [HasLeftHomology S]

theorem liftCycles_comp_cyclesMap (φ : S ⟶ S₁) [S₁.HasLeftHomology] :
    S.liftCycles k hk ≫ CategoryTheory.ShortComplex.cyclesMap φ =
      S₁.liftCycles (k ≫ φ.τ₂) (by rw [assoc, φ.comm₂₃, reassoc_of% hk, zero_comp]) := by
  cat_disch

