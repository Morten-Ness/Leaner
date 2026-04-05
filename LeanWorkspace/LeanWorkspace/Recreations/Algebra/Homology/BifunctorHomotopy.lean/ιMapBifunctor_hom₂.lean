import Mathlib

variable {C₁ C₂ D I₁ I₂ J : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

variable {K₁ L₁ : HomologicalComplex C₁ c₁} {f₁ f₁' : K₁ ⟶ L₁} (h₁ : Homotopy f₁ f₁')
  {K₂ L₂ : HomologicalComplex C₂ c₂} (f₂ f₂' : K₂ ⟶ L₂) (h₂ : Homotopy f₂ f₂')
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c]

theorem ιMapBifunctor_hom₂ (i₁ : I₁) (i₂ i₂' : I₂) (j j' : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂') = j) (h' : c₂.prev i₂' = i₂) :
    ιMapBifunctor K₁ K₂ F c i₁ i₂' j h ≫ HomologicalComplex.mapBifunctorMapHomotopy.hom₂ f₁ h₂ F c j j' =
      ComplexShape.ε₂ c₁ c₂ c (i₁, i₂) •
        (F.map (f₁.f i₁)).app (K₂.X i₂') ≫
          (F.obj (L₁.X i₁)).map (h₂.hom i₂' i₂) ≫ ιMapBifunctorOrZero L₁ L₂ F c i₁ i₂ j' := by
  subst h'
  simp [HomologicalComplex.mapBifunctorMapHomotopy.hom₂]

