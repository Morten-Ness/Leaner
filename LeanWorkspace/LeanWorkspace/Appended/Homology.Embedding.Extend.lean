import Mathlib

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

set_option backward.isDefEq.respectTransparency false in
theorem XOpIso_hom_d_op (i j : Option ι) :
    (HomologicalComplex.extend.XOpIso K i).hom ≫ (HomologicalComplex.extend.d K j i).op =
      HomologicalComplex.extend.d K.op i j ≫ (HomologicalComplex.extend.XOpIso K j).hom := match i, j with
  | none, _ => by
      simp only [HomologicalComplex.extend.d_none_eq_zero, HomologicalComplex.extend.d_none_eq_zero', comp_zero, zero_comp, op_zero]
  | some i, some j => by
      dsimp [HomologicalComplex.extend.XOpIso]
      simp only [HomologicalComplex.extend.d_eq _ rfl rfl, op_comp, assoc, id_comp, comp_id]
      rfl
  | some _, none => by
      simp only [HomologicalComplex.extend.d_none_eq_zero, HomologicalComplex.extend.d_none_eq_zero', comp_zero, zero_comp, op_zero]

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem d_eq {i j : Option ι} {a b : ι} (hi : i = some a) (hj : j = some b) :
    HomologicalComplex.extend.d K i j = (HomologicalComplex.extend.XIso K hi).hom ≫ K.d a b ≫ (HomologicalComplex.extend.XIso K hj).inv := by
  subst hi hj
  simp [HomologicalComplex.extend.XIso, HomologicalComplex.extend.X, HomologicalComplex.extend.d]

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

theorem extendMap_add [Preadditive C] {K L : HomologicalComplex C c} (φ φ' : K ⟶ L)
    (e : c.Embedding c') : HomologicalComplex.extendMap (φ + φ' : K ⟶ L) e = HomologicalComplex.extendMap φ e + HomologicalComplex.extendMap φ' e := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [HomologicalComplex.extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem extendMap_comp :
    HomologicalComplex.extendMap (φ ≫ φ') e = HomologicalComplex.extendMap φ e ≫ HomologicalComplex.extendMap φ' e := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [HomologicalComplex.extendMap_f _ e hi]
  · simp [HomologicalComplex.extendMap_f_eq_zero _ e i' (fun i hi => hi' ⟨i, hi⟩)]

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem extendMap_f {i : ι} {i' : ι'} (h : e.f i = i') :
    (HomologicalComplex.extendMap φ e).f i' =
      (HomologicalComplex.extendXIso K e h).hom ≫ φ.f i ≫ (HomologicalComplex.extendXIso L e h).inv := by
  dsimp [HomologicalComplex.extendMap]
  rw [HomologicalComplex.extend.mapX_some HomologicalComplex.extend φ (e.r_eq_some h)]
  rfl

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

set_option backward.isDefEq.respectTransparency false in
theorem extendMap_f_eq_zero (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    (HomologicalComplex.extendMap φ e).f i' = 0 := by
  dsimp [HomologicalComplex.extendMap]
  rw [HomologicalComplex.extend.mapX_none HomologicalComplex.extend φ (e.r_eq_none i' hi')]

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem extendMap_id : HomologicalComplex.extendMap (𝟙 K) e = 𝟙 _ := by
  ext
  simpa using HomologicalComplex.extendMap_id_f _ _ _

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem extendMap_id_f (i' : ι') : (HomologicalComplex.extendMap (𝟙 K) e).f i' = 𝟙 _ := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [HomologicalComplex.extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem extendMap_zero : HomologicalComplex.extendMap (0 : K ⟶ L) e = 0 := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [HomologicalComplex.extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] [DecidableEq ι]
  (e : c.Embedding c') (X : C)

variable [DecidableEq ι'] (i : ι) (i' : ι')

theorem extendSingleIso_hom_f (h : e.f i = i') :
    (HomologicalComplex.extendSingleIso e HomologicalComplex.extend.X i i' h).hom.f i' =
      (((single C c i).obj HomologicalComplex.extend.X).extendXIso e h).hom ≫ (singleObjXSelf c i HomologicalComplex.extend.X).hom ≫
        (singleObjXSelf c' i' HomologicalComplex.extend.X).inv := by
  simp [HomologicalComplex.extendSingleIso]

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] [DecidableEq ι]
  (e : c.Embedding c') (X : C)

variable [DecidableEq ι'] (i : ι) (i' : ι')

theorem extendSingleIso_inv_f (h : e.f i = i') :
    (HomologicalComplex.extendSingleIso e HomologicalComplex.extend.X i i' h).inv.f i' =
      (singleObjXSelf c' i' HomologicalComplex.extend.X).hom ≫ (singleObjXSelf c i HomologicalComplex.extend.X).inv ≫
        (((single C c i).obj HomologicalComplex.extend.X).extendXIso e h).inv := by
  simp [HomologicalComplex.extendSingleIso]

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem extend_d_eq {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j') :
    (K.extend e).d i' j' = (K.extendXIso e hi).hom ≫ K.d i j ≫
      (K.extendXIso e hj).inv := by
  apply HomologicalComplex.extend.d_eq HomologicalComplex.extend

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem extend_d_from_eq_zero (i' j' : ι') (i : ι) (hi : e.f i = i') (hi' : ¬ c.Rel i (c.next i)) :
    (K.extend e).d i' j' = 0 := by
  obtain hj' | ⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
  · exact HomologicalComplex.extend.d_none_eq_zero' HomologicalComplex.extend _ _ _ hj'
  · rw [HomologicalComplex.extend_d_eq K e hi (e.f_eq_of_r_eq_some hj), K.shape, zero_comp, comp_zero]
    intro hij
    obtain rfl := c.next_eq' hij
    exact hi' hij

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem extend_d_to_eq_zero (i' j' : ι') (j : ι) (hj : e.f j = j') (hj' : ¬ c.Rel (c.prev j) j) :
    (K.extend e).d i' j' = 0 := by
  obtain hi' | ⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
  · exact HomologicalComplex.extend.d_none_eq_zero HomologicalComplex.extend _ _ _ hi'
  · rw [HomologicalComplex.extend_d_eq K e (e.f_eq_of_r_eq_some hi) hj, K.shape, zero_comp, comp_zero]
    intro hij
    obtain rfl := c.prev_eq' hij
    exact hj' hij

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

set_option backward.isDefEq.respectTransparency false in
theorem extend_op_d (i' j' : ι') :
    (K.op.extend e.op).d i' j' =
      (K.extendOpIso e).hom.f i' ≫ ((K.extend e).d j' i').op ≫
        (K.extendOpIso e).inv.f j' := by
  have := (K.extendOpIso e).inv.comm i' j'
  dsimp at this
  rw [← this, ← comp_f_assoc, Iso.hom_inv_id, id_f, id_comp]

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] [DecidableEq ι]
  (e : c.Embedding c') (X : C)

theorem extend_single_d (i : ι) (j' k' : ι') :
    (((single C c i).obj HomologicalComplex.extend.X).extend e).d j' k' = 0 := by
  by_cases hj : ∃ j, e.f j = j'
  · obtain ⟨j, rfl⟩ := hj
    by_cases hk : ∃ k, e.f k = k'
    · obtain ⟨k, rfl⟩ := hk
      simp [HomologicalComplex.extend_d_eq _ _ rfl rfl]
    · exact IsZero.eq_of_tgt (HomologicalComplex.isZero_extend_X _ _ _ (by tauto)) _ _
  · exact IsZero.eq_of_src (HomologicalComplex.isZero_extend_X _ _ _ (by tauto)) _ _

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem isZero_X {i : Option ι} (hi : i = none) :
    IsZero (HomologicalComplex.extend.X K i) := by
  subst hi
  exact Limits.isZero_zero _

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem isZero_extend_X' (i' : ι') (hi' : e.r i' = none) :
    IsZero ((K.extend e).X i') := HomologicalComplex.extend.isZero_X HomologicalComplex.extend K hi'

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem isZero_extend_X (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsZero ((K.extend e).X i') := K.isZero_extend_X' e i' (ComplexShape.Embedding.r_eq_none e i' hi')

end

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem mapX_some {i : Option ι} {a : ι} (hi : i = some a) :
    HomologicalComplex.extend.mapX φ i = (HomologicalComplex.extend.XIso K hi).hom ≫ φ.f a ≫ (HomologicalComplex.extend.XIso L hi).inv := by
  subst hi
  dsimp [HomologicalComplex.extend.XIso, HomologicalComplex.extend.X]
  rw [id_comp, comp_id]
  rfl

end
