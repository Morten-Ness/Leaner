import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable (S) (h : LeftHomologyData S) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0)
  [HasLeftHomology S]

theorem toCycles_comp_leftHomologyπ : S.toCycles ≫ S.leftHomologyπ = 0 := S.liftCycles_leftHomologyπ_eq_zero_of_boundary S.f (𝟙 _) (by rw [id_comp])

