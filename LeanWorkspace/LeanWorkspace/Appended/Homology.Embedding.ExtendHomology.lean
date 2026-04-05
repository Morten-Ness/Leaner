import Mathlib

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] [L.HasHomology j]
  [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j']

theorem extendHomologyIso_hom_naturality :
    homologyMap (extendMap φ e) j' ≫ (L.extendHomologyIso e hj').hom =
      (K.extendHomologyIso e hj').hom ≫ homologyMap φ j := by
  simp [← cancel_epi ((K.extend e).homologyπ _)]

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] [L.HasHomology j]
  [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j']

theorem extendHomologyIso_inv_homologyι :
    (K.extendHomologyIso e hj').inv ≫ (K.extend e).homologyι j' =
      K.homologyι j ≫ (K.extendOpcyclesIso e hj').inv := by
  simp only [← cancel_epi (K.extendHomologyIso e hj').hom,
    Iso.hom_inv_id_assoc, extendHomologyIso_hom_homologyι_assoc, Iso.hom_inv_id, comp_id]

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] [L.HasHomology j]
  [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j']

include hj' in
theorem extend_exactAt_iff :
    (K.extend e).ExactAt j' ↔ K.ExactAt j := by
  simp only [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (K.extendHomologyIso e hj').isZero_iff

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem hasHomology {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] :
    (K.extend e).HasHomology j' := ShortComplex.HasHomology.mk'
    (HomologicalComplex.extend.homologyData' K e hj' rfl rfl ((K.sc j).homologyData))

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] [L.HasHomology j]
  [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j']

set_option backward.isDefEq.respectTransparency false in
theorem homologyπ_extendHomologyIso_hom :
    (K.extend e).homologyπ j' ≫ (K.extendHomologyIso e hj').hom =
      (K.extendCyclesIso e hj').hom ≫ K.homologyπ j := by
  dsimp [HomologicalComplex.extendHomologyIso, homologyπ]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc,
    ← cancel_mono (K.sc j).homologyData.left.homologyIso.hom,
    assoc, assoc, assoc, Iso.inv_hom_id, comp_id,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  dsimp [HomologicalComplex.extendCyclesIso]
  simp only [assoc, Iso.inv_hom_id_assoc]

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] [L.HasHomology j]
  [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j']

theorem homologyπ_extendHomologyIso_inv :
    K.homologyπ j ≫ (K.extendHomologyIso e hj').inv =
      (K.extendCyclesIso e hj').inv ≫ (K.extend e).homologyπ j' := by
  simp only [← cancel_mono (K.extendHomologyIso e hj').hom,
    assoc, Iso.inv_hom_id, comp_id, HomologicalComplex.homologyπ_extendHomologyIso_hom, Iso.inv_hom_id_assoc]

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {i j k : ι} {i' j' k' : ι'} (hj' : e.f j = j')
  (hi : c.prev j = i) (hi' : c'.prev j' = i') (hk : c.next j = k) (hk' : c'.next j' = k')

variable (cone : KernelFork (K.d j k)) (hcone : IsLimit cone)

variable (cocone : CokernelCofork (hcone.lift (KernelFork.ofι (K.d i j) (K.d_comp_d i j k))))
  (hcocone : IsColimit cocone)

include hi hi' hcone in
theorem lift_d_comp_eq_zero_iff' ⦃W : C⦄ (f' : K.X i ⟶ cone.pt)
    (hf' : f' ≫ cone.ι = K.d i j)
    (f'' : (K.extend e).X i' ⟶ cone.pt)
    (hf'' : f'' ≫ cone.ι ≫ (extendXIso K e hj').inv = (K.extend e).d i' j')
    (φ : cone.pt ⟶ W) :
    f' ≫ φ = 0 ↔ f'' ≫ φ = 0 := by
  by_cases hij : c.Rel i j
  · have hi'' : e.f i = i' := by rw [← hi', ← hj', c'.prev_eq' (e.rel hij)]
    have : (K.extendXIso e hi'').hom ≫ f' = f'' := by
      apply Fork.IsLimit.hom_ext hcone
      rw [assoc, hf', ← cancel_mono (extendXIso K e hj').inv, assoc, assoc, hf'',
        K.extend_d_eq e hi'' hj']
    rw [← cancel_epi (K.extendXIso e hi'').hom, comp_zero, ← this, assoc]
  · have h₁ : f' = 0 := by
      apply Fork.IsLimit.hom_ext hcone
      simp only [zero_comp, hf', K.shape _ _ hij]
    have h₂ : f'' = 0 := by
      apply Fork.IsLimit.hom_ext hcone
      dsimp
      rw [← cancel_mono (extendXIso K e hj').inv, assoc, hf'', zero_comp, zero_comp,
        K.extend_d_to_eq_zero e i' j' j hj']
      rw [hi]
      exact hij
    simp [h₁, h₂]

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {i j k : ι} {i' j' k' : ι'} (hj' : e.f j = j')
  (hi : c.prev j = i) (hi' : c'.prev j' = i') (hk : c.next j = k) (hk' : c'.next j' = k')

variable (cone : KernelFork (K.d j k)) (hcone : IsLimit cone)

variable (cocone : CokernelCofork (hcone.lift (KernelFork.ofι (K.d i j) (K.d_comp_d i j k))))
  (hcocone : IsColimit cocone)

include hi hi' in
theorem lift_d_comp_eq_zero_iff ⦃W : C⦄ (φ : cone.pt ⟶ W) :
    hcone.lift (KernelFork.ofι (K.d i j) (K.d_comp_d i j k)) ≫ φ = 0 ↔
      ((HomologicalComplex.extend.leftHomologyData.isLimitKernelFork K e hj' hk hk' cone hcone).lift
      (KernelFork.ofι ((K.extend e).d i' j') (d_comp_d _ _ _ _))) ≫ φ = 0 := HomologicalComplex.extend.leftHomologyData.lift_d_comp_eq_zero_iff' K e hj' hi hi' cone hcone _ (hcone.fac _ _) _
    (IsLimit.fac _ _ WalkingParallelPair.zero) _

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] [L.HasHomology j]
  [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j']

theorem pOpcycles_extendOpcyclesIso_hom :
    (K.extend e).pOpcycles j' ≫ (K.extendOpcyclesIso e hj').hom =
      (K.extendXIso e hj').hom ≫ K.pOpcycles j := by
  simp only [← cancel_mono (K.extendOpcyclesIso e hj').inv,
    assoc, Iso.hom_inv_id, comp_id, HomologicalComplex.pOpcycles_extendOpcyclesIso_inv, Iso.hom_inv_id_assoc]

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] [L.HasHomology j]
  [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j']

set_option backward.isDefEq.respectTransparency false in
theorem pOpcycles_extendOpcyclesIso_inv :
    K.pOpcycles j ≫ (K.extendOpcyclesIso e hj').inv =
      (K.extendXIso e hj').inv ≫ (K.extend e).pOpcycles j' := by
  rw [← cancel_mono (K.extendOpcyclesIso e hj').hom, assoc, assoc, Iso.inv_hom_id, comp_id]
  dsimp [HomologicalComplex.extendOpcyclesIso, pOpcycles]
  rw [ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom_assoc]
  dsimp
  rw [assoc, Iso.inv_hom_id_assoc, ShortComplex.RightHomologyData.p_comp_opcyclesIso_inv]
  rfl

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] [L.HasHomology j]
  [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j']

include hj' in
theorem quasiIsoAt_extendMap_iff :
    QuasiIsoAt (extendMap φ e) j' ↔ QuasiIsoAt φ j := by
  simp only [quasiIsoAt_iff_isIso_homologyMap]
  exact (MorphismProperty.isomorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.extendHomologyIso e hj') (L.extendHomologyIso e hj'))

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem quasiIso_extendMap_iff [∀ j, K.HasHomology j] [∀ j, L.HasHomology j] :
    QuasiIso (extendMap φ e) ↔ QuasiIso φ := by
  simp only [quasiIso_iff, ← fun j ↦ HomologicalComplex.quasiIsoAt_extendMap_iff φ e (j := j) (hj' := rfl)]
  constructor
  · tauto
  · intro h j'
    by_cases hj' : ∃ j, e.f j = j'
    · obtain ⟨j, rfl⟩ := hj'
      exact h j
    · rw [quasiIsoAt_iff_exactAt]
      all_goals
        exact HomologicalComplex.extend_exactAt _ _ _ (by simpa using hj')

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {i j k : ι} {i' j' k' : ι'} (hj' : e.f j = j')
  (hi : c.prev j = i) (hi' : c'.prev j' = i') (hk : c.next j = k) (hk' : c'.next j' = k')

set_option backward.isDefEq.respectTransparency false in
theorem rightHomologyData_g' (h : (K.sc' i j k).RightHomologyData) (hk'' : e.f k = k') :
    (HomologicalComplex.extend.rightHomologyData K e hj' hi hi' hk hk' h).g' = h.g' ≫ (K.extendXIso e hk'').inv := by
  rw [← cancel_epi h.p, ← cancel_epi (extendXIso K e hj').hom]
  have := (HomologicalComplex.extend.rightHomologyData K e hj' hi hi' hk hk' h).p_g'
  dsimp at this
  rw [assoc] at this
  rw [this, K.extend_d_eq e hj' hk'', h.p_g'_assoc, shortComplexFunctor'_obj_g]

end
