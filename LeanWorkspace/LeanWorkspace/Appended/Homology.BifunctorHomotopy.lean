import Mathlib

section

variable {C₁ C₂ D I₁ I₂ J : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

variable {K₁ L₁ : HomologicalComplex C₁ c₁} {f₁ f₁' : K₁ ⟶ L₁} (h₁ : Homotopy f₁ f₁')
  {K₂ L₂ : HomologicalComplex C₂ c₂} (f₂ f₂' : K₂ ⟶ L₂) (h₂ : Homotopy f₂ f₂')
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c]

theorem comm₁ (j : J) :
    (mapBifunctorMap f₁ f₂ F c).f j =
    (mapBifunctor K₁ K₂ F c).d j (c.next j) ≫
          HomologicalComplex.mapBifunctorMapHomotopy.hom₁ h₁ f₂ F c (c.next j) j +
        HomologicalComplex.mapBifunctorMapHomotopy.hom₁ h₁ f₂ F c j (c.prev j) ≫
          (mapBifunctor L₁ L₂ F c).d (c.prev j) j +
      (mapBifunctorMap f₁' f₂ F c).f j := by
  ext i₁ i₂ h
  simp? [HomologicalComplex₂.total_d, h₁.comm i₁, dFrom, fromNext, toPrev, dTo] says
    simp only [ι_mapBifunctorMap, h₁.comm i₁, dNext_eq_dFrom_fromNext, dFrom, fromNext,
      AddMonoidHom.mk'_apply, prevD_eq_toPrev_dTo, toPrev, dTo, Functor.map_add,
      Functor.map_comp, NatTrans.app_add, NatTrans.comp_app,
      Preadditive.add_comp, assoc, HomologicalComplex₂.total_d,
      Functor.mapBifunctorHomologicalComplex_obj_obj_toGradedObject, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁_assoc, Functor.mapBifunctorHomologicalComplex_obj_obj_X_X,
      HomologicalComplex₂.ι_D₂_assoc, add_left_inj]
  have : ∀ {X Y : D} (a b c d e f : X ⟶ Y), a = c → b = e → f = -d →
      a + b = c + d + (e + f) := by rintro X Y a b _ d _ _ rfl rfl rfl; abel
  apply this
  · by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
    · rw [HomologicalComplex₂.d₁_eq _ _ h₃ _ _ (by rw [← h, ComplexShape.next_π₁ c₂ c h₃]),
        Functor.mapBifunctorHomologicalComplex_obj_obj_d_f, Linear.units_smul_comp, assoc,
        HomologicalComplex.mapBifunctorMapHomotopy.ιMapBifunctor_hom₁ _ _ _ _ i₁ _ _ _ _ _ (c₁.prev_eq' h₃),
        Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul,
        ιMapBifunctorOrZero_eq]
    · rw [K₁.shape _ _ h₃, Functor.map_zero, zero_app, zero_comp,
        HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ h₃, zero_comp]
  · rw [ιMapBifunctor_hom₁_assoc _ _ _ _ _ _ _ _ _ _ rfl]
    by_cases h₃ : c₁.Rel (c₁.prev i₁) i₁
    · rw [ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ (by rw [← ComplexShape.prev_π₁ c₂ c h₃, h]),
        Linear.units_smul_comp, assoc, assoc, HomologicalComplex₂.ι_D₁,
        HomologicalComplex₂.d₁_eq _ _ h₃ _ _ h, Linear.comp_units_smul,
        Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul,
        Functor.mapBifunctorHomologicalComplex_obj_obj_d_f, NatTrans.naturality_assoc]
    · rw [h₁.zero _ _ h₃, Functor.map_zero, zero_app, zero_comp, zero_comp, smul_zero, zero_comp]
  · rw [ιMapBifunctor_hom₁_assoc _ _ _ _ _ _ _ _ _ _ rfl]
    by_cases h₃ : c₁.Rel (c₁.prev i₁) i₁
    · dsimp
      rw [Linear.units_smul_comp, assoc, assoc,
        ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ (by rw [← ComplexShape.prev_π₁ c₂ c h₃, h]),
        HomologicalComplex₂.ι_D₂]
      by_cases h₄ : c₂.Rel i₂ (c₂.next i₂)
      · exact HomologicalComplex.mapBifunctorMapHomotopy.comm₁_aux h₁ f₂ F c h₃ h₄ j h
      · rw [HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ h₄, comp_zero, comp_zero, smul_zero,
          HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ h₄, zero_comp, neg_zero]
    · rw [h₁.zero _ _ h₃, Functor.map_zero, zero_app, zero_comp,
        smul_zero, zero_comp, zero_eq_neg]
      by_cases h₄ : c₂.Rel i₂ (c₂.next i₂)
      · by_cases h₅ : c.Rel j (c.next j)
        · rw [HomologicalComplex₂.d₂_eq _ _ _ h₄ _ (by rw [← ComplexShape.next_π₂ c₁ c i₁ h₄, h]),
            Linear.units_smul_comp, assoc, Functor.mapBifunctorHomologicalComplex_obj_obj_X_d,
            HomologicalComplex.mapBifunctorMapHomotopy.ιMapBifunctor_hom₁ _ _ _ _ _ _ _ _ _ _ rfl, h₁.zero _ _ h₃,
            Functor.map_zero, zero_app, zero_comp, smul_zero, comp_zero, smul_zero]
        · rw [HomologicalComplex.mapBifunctorMapHomotopy.zero₁ _ _ _ _ _ _ h₅, comp_zero]
      · rw [HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ h₄, zero_comp]

end

section

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

end

section

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

end

section

variable {C₁ C₂ D I₁ I₂ J : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

variable {K₁ L₁ : HomologicalComplex C₁ c₁} {f₁ f₁' : K₁ ⟶ L₁} (h₁ : Homotopy f₁ f₁')
  {K₂ L₂ : HomologicalComplex C₂ c₂} (f₂ f₂' : K₂ ⟶ L₂) (h₂ : Homotopy f₂ f₂')
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c]

theorem ιMapBifunctor_hom₁ (i₁ i₁' : I₁) (i₂ : I₂) (j j' : J)
    (h : ComplexShape.π c₁ c₂ c (i₁', i₂) = j) (h' : c₁.prev i₁' = i₁) :
    ιMapBifunctor K₁ K₂ F c i₁' i₂ j h ≫ HomologicalComplex.mapBifunctorMapHomotopy.hom₁ h₁ f₂ F c j j' = ComplexShape.ε₁ c₁ c₂ c (i₁, i₂) •
      (F.map (h₁.hom i₁' i₁)).app (K₂.X i₂) ≫ (F.obj (L₁.X i₁)).map (f₂.f i₂) ≫
        ιMapBifunctorOrZero L₁ L₂ F c _ _ j' := by
  subst h'
  simp [HomologicalComplex.mapBifunctorMapHomotopy.hom₁]

end

section

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

end
