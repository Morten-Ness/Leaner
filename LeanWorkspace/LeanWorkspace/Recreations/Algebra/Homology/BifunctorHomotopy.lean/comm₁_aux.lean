import Mathlib

variable {C₁ C₂ D I₁ I₂ J : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

variable {K₁ L₁ : HomologicalComplex C₁ c₁} {f₁ f₁' : K₁ ⟶ L₁} (h₁ : Homotopy f₁ f₁')
  {K₂ L₂ : HomologicalComplex C₂ c₂} (f₂ f₂' : K₂ ⟶ L₂) (h₂ : Homotopy f₂ f₂')
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c]

theorem comm₁_aux {i₁ i₁' : I₁} (hi₁ : c₁.Rel i₁ i₁') {i₂ i₂' : I₂} (hi₂ : c₂.Rel i₂ i₂') (j : J)
    (hj : ComplexShape.π c₁ c₂ c (i₁', i₂) = j) :
    ComplexShape.ε₁ c₁ c₂ c (i₁, i₂) • (F.map (h₁.hom i₁' i₁)).app (K₂.X i₂) ≫
      (F.obj (L₁.X i₁)).map (f₂.f i₂) ≫
        (((F.mapBifunctorHomologicalComplex c₁ c₂).obj L₁).obj L₂).d₂ c i₁ i₂ j =
    -(((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).d₂ c i₁' i₂ (c.next j) ≫
      HomologicalComplex.mapBifunctorMapHomotopy.hom₁ h₁ f₂ F c (c.next j) j := by
  have hj' : ComplexShape.π c₁ c₂ c ⟨i₁, i₂'⟩ = j := by
    rw [← hj, ← ComplexShape.next_π₂ c₁ c i₁ hi₂, ComplexShape.next_π₁ c₂ c hi₁ i₂]
  rw [HomologicalComplex₂.d₂_eq _ _ _ hi₂ _ hj', HomologicalComplex₂.d₂_eq _ _ _ hi₂ _
        (by rw [← c.next_eq' (ComplexShape.rel_π₂ c₁ c i₁' hi₂), hj]),
    Linear.comp_units_smul, Linear.comp_units_smul, Linear.units_smul_comp, assoc,
    HomologicalComplex.mapBifunctorMapHomotopy.ιMapBifunctor_hom₁ _ _ _ _ _ _ _ _ _ _ (c₁.prev_eq' hi₁),
    ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hj',
    Linear.comp_units_smul, smul_smul, smul_smul,
    Functor.mapBifunctorHomologicalComplex_obj_obj_X_d,
    Functor.mapBifunctorHomologicalComplex_obj_obj_X_d,
    NatTrans.naturality_assoc, ComplexShape.ε₁_ε₂ c hi₁ hi₂, neg_mul, Units.neg_smul, neg_inj,
    smul_left_cancel_iff, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, f₂.comm]

