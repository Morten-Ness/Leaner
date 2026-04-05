import Mathlib

section

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

variable [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [DecidableEq J]

variable (i₁ : I₁) (i₂ : I₂) (j : J)

theorem d₁_eq' {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (j : J) :
    HomologicalComplex.mapBifunctor.d₁ K₁ K₂ F c i₁ i₂ j = ComplexShape.ε₁ c₁ c₂ c ⟨i₁, i₂⟩ •
      ((F.map (K₁.d i₁ i₁')).app (K₂.X i₂) ≫ ιMapBifunctorOrZero K₁ K₂ F c i₁' i₂ j) := HomologicalComplex₂.d₁_eq' _ _ h _ _

end

section

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

variable [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [DecidableEq J]

variable (i₁ : I₁) (i₂ : I₂) (j : J)

theorem d₁_eq {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (j : J)
    (h' : ComplexShape.π c₁ c₂ c ⟨i₁', i₂⟩ = j) :
    HomologicalComplex.mapBifunctor.d₁ K₁ K₂ F c i₁ i₂ j = ComplexShape.ε₁ c₁ c₂ c ⟨i₁, i₂⟩ •
      ((F.map (K₁.d i₁ i₁')).app (K₂.X i₂) ≫ ιMapBifunctor K₁ K₂ F c i₁' i₂ j h') := HomologicalComplex₂.d₁_eq _ _ h _ _ h'

end

section

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

variable [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [DecidableEq J]

variable (i₁ : I₁) (i₂ : I₂) (j : J)

theorem d₁_eq_zero' {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (j : J)
    (h' : ComplexShape.π c₁ c₂ c ⟨i₁', i₂⟩ ≠ j) :
    HomologicalComplex.mapBifunctor.d₁ K₁ K₂ F c i₁ i₂ j = 0 := HomologicalComplex₂.d₁_eq_zero' _ _ h _ _ h'

end

section

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

variable [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [DecidableEq J]

variable (i₁ : I₁) (i₂ : I₂) (j : J)

theorem d₁_eq_zero (h : ¬ c₁.Rel i₁ (c₁.next i₁)) :
    HomologicalComplex.mapBifunctor.d₁ K₁ K₂ F c i₁ i₂ j = 0 := HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ h

end

section

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

variable [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [DecidableEq J]

variable (i₁ : I₁) (i₂ : I₂) (j : J)

theorem d₂_eq' (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (j : J) :
    HomologicalComplex.mapBifunctor.d₂ K₁ K₂ F c i₁ i₂ j = ComplexShape.ε₂ c₁ c₂ c ⟨i₁, i₂⟩ •
      ((F.obj (K₁.X i₁)).map (K₂.d i₂ i₂') ≫ ιMapBifunctorOrZero K₁ K₂ F c i₁ i₂' j) := HomologicalComplex₂.d₂_eq' _ _ _ h _

end

section

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

variable [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [DecidableEq J]

variable (i₁ : I₁) (i₂ : I₂) (j : J)

theorem d₂_eq (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (j : J)
    (h' : ComplexShape.π c₁ c₂ c ⟨i₁, i₂'⟩ = j) :
    HomologicalComplex.mapBifunctor.d₂ K₁ K₂ F c i₁ i₂ j = ComplexShape.ε₂ c₁ c₂ c ⟨i₁, i₂⟩ •
      ((F.obj (K₁.X i₁)).map (K₂.d i₂ i₂') ≫ ιMapBifunctor K₁ K₂ F c i₁ i₂' j h') := HomologicalComplex₂.d₂_eq _ _ _ h _ h'

end

section

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

variable [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [DecidableEq J]

variable (i₁ : I₁) (i₂ : I₂) (j : J)

theorem d₂_eq_zero' (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (j : J)
    (h' : ComplexShape.π c₁ c₂ c ⟨i₁, i₂'⟩ ≠ j) :
    HomologicalComplex.mapBifunctor.d₂ K₁ K₂ F c i₁ i₂ j = 0 := HomologicalComplex₂.d₂_eq_zero' _ _ _ h _ h'

end

section

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

variable [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [DecidableEq J]

variable (i₁ : I₁) (i₂ : I₂) (j : J)

theorem d₂_eq_zero (h : ¬ c₂.Rel i₂ (c₂.next i₂)) :
    HomologicalComplex.mapBifunctor.d₂ K₁ K₂ F c i₁ i₂ j = 0 := HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ h

end

section

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

variable [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [DecidableEq J]

theorem hom_ext {Y : D} {j : J} {f g : (HomologicalComplex.mapBifunctor K₁ K₂ F c).X j ⟶ Y}
    (h : ∀ (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c ⟨i₁, i₂⟩ = j),
      ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ f = ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ g) :
    f = g := HomologicalComplex₂.total.hom_ext _ h

end

section

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

variable [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [DecidableEq J]

variable (j j' : J) (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j)

theorem ι_D₁ :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ HomologicalComplex.mapBifunctor.D₁ K₁ K₂ F c j j' = HomologicalComplex.mapBifunctor.d₁ K₁ K₂ F c i₁ i₂ j' := by
  apply HomologicalComplex₂.ι_D₁

end

section

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

variable [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [DecidableEq J]

variable (j j' : J) (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j)

theorem ι_D₂ :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ HomologicalComplex.mapBifunctor.D₂ K₁ K₂ F c j j' = HomologicalComplex.mapBifunctor.d₂ K₁ K₂ F c i₁ i₂ j' := by
  apply HomologicalComplex₂.ι_D₂

end

section

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

variable [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [DecidableEq J]

variable {A : D} {j : J}
  (f : ∀ (i₁ : I₁) (i₂ : I₂) (_ : ComplexShape.π c₁ c₂ c ⟨i₁, i₂⟩ = j),
    (F.obj (K₁.X i₁)).obj (K₂.X i₂) ⟶ A)

theorem ι_mapBifunctorDesc (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c ⟨i₁, i₂⟩ = j) :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ HomologicalComplex.mapBifunctorDesc f = f i₁ i₂ h := by
  apply HomologicalComplex₂.ι_totalDesc

end

section

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

variable [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [DecidableEq J]

set_option backward.isDefEq.respectTransparency false in
theorem ι_mapBifunctorMap (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ (HomologicalComplex.mapBifunctorMap f₁ f₂ F c).f j =
      (F.map (f₁.f i₁)).app (K₂.X i₂) ≫ (F.obj (L₁.X i₁)).map (f₂.f i₂) ≫
        ιMapBifunctor L₁ L₂ F c i₁ i₂ j h := by
  simp [HomologicalComplex.mapBifunctorMap]

end
