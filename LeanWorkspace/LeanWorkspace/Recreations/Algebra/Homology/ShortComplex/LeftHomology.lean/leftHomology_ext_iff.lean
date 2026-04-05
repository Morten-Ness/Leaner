import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasLeftHomology]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
theorem leftHomology_ext_iff {A : C} (f₁ f₂ : S.leftHomology ⟶ A) :
    f₁ = f₂ ↔ S.leftHomologyπ ≫ f₁ = S.leftHomologyπ ≫ f₂ := by
  rw [cancel_epi]

