import Mathlib

variable {C₁ C₂ D I₁ I₂ J : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

variable {K₁ L₁ : HomologicalComplex C₁ c₁} {f₁ f₁' : K₁ ⟶ L₁} (h₁ : Homotopy f₁ f₁')
  {K₂ L₂ : HomologicalComplex C₂ c₂} (f₂ f₂' : K₂ ⟶ L₂) (h₂ : Homotopy f₂ f₂')
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c]

theorem zero₁ (j j' : J) (h : ¬ c.Rel j' j) :
    HomologicalComplex.mapBifunctorMapHomotopy.hom₁ h₁ f₂ F c j j' = 0 := by
  ext i₁ i₂ h'
  dsimp [HomologicalComplex.mapBifunctorMapHomotopy.hom₁]
  rw [comp_zero, HomologicalComplex₂.ι_totalDesc]
  by_cases h₃ : c₁.Rel (c₁.prev i₁) i₁
  · rw [ιMapBifunctorOrZero_eq_zero, comp_zero, comp_zero, smul_zero]
    intro h₄
    apply h
    rw [← h', ← h₄]
    exact ComplexShape.rel_π₁ c₂ c h₃ i₂
  · dsimp
    rw [h₁.zero _ _ h₃, Functor.map_zero, zero_app, zero_comp, smul_zero]

