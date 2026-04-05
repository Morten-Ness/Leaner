import Mathlib

section

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

theorem Quot.addMonoidHom_ext [DecidableEq J] {α : Type*} [AddMonoid α] {f g : AddCommGrpCat.Colimits.Quot F →+ α}
    (h : ∀ (j : J) (x : F.obj j), f (AddCommGrpCat.Colimits.Quot.ι F j x) = g (AddCommGrpCat.Colimits.Quot.ι F j x)) : f = g := QuotientAddGroup.addMonoidHom_ext _ (DFinsupp.addHom_ext h)

end

section

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

variable (c : Cocone F)

theorem Quot.desc_colimitCocone [DecidableEq J] (F : J ⥤ AddCommGrpCat.{w}) [Small.{w} (AddCommGrpCat.Colimits.Quot F)] :
    AddCommGrpCat.Colimits.Quot.desc F (AddCommGrpCat.Colimits.colimitCocone F) = (Shrink.addEquiv (α := AddCommGrpCat.Colimits.Quot F)).symm.toAddMonoidHom := by
  refine AddCommGrpCat.Colimits.Quot.addMonoidHom_ext F (fun j x ↦ ?_)
  simpa only [colimitCocone_pt, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    using AddCommGrpCat.Colimits.Quot.ι_desc F (AddCommGrpCat.Colimits.colimitCocone F) j x

end

section

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

variable (c : Cocone F)

set_option backward.isDefEq.respectTransparency false in
theorem Quot.desc_quotQuotUliftAddEquiv [DecidableEq J] (c : Cocone F) :
    (AddCommGrpCat.Colimits.Quot.desc (F ⋙ uliftFunctor.{u'}) (uliftFunctor.{u'}.mapCocone c)).comp
    (AddCommGrpCat.Colimits.quotQuotUliftAddEquiv F).toAddMonoidHom =
    AddEquiv.ulift.symm.toAddMonoidHom.comp (AddCommGrpCat.Colimits.Quot.desc F c) := by
  refine AddCommGrpCat.Colimits.Quot.addMonoidHom_ext _ (fun j a ↦ ?_)
  dsimp
  simp only [AddCommGrpCat.Colimits.quotToQuotUlift_ι, Functor.comp_obj, uliftFunctor_obj, ι_desc, Functor.const_obj_obj,
    ι_desc]
  erw [AddCommGrpCat.Colimits.Quot.ι_desc]
  rfl

end

section

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

variable (c : Cocone F)

set_option backward.isDefEq.respectTransparency false in
theorem Quot.desc_toCocone_desc [DecidableEq J] {A : Type w} [AddCommGroup A] (f : AddCommGrpCat.Colimits.Quot F →+ A)
    (hc : IsColimit c) : (hc.desc (AddCommGrpCat.Colimits.toCocone F f)).hom.comp (AddCommGrpCat.Colimits.Quot.desc F c) = f := by
  refine AddCommGrpCat.Colimits.Quot.addMonoidHom_ext F (fun j x ↦ ?_)
  rw [AddMonoidHom.comp_apply, ι_desc]
  change (c.ι.app j ≫ hc.desc (AddCommGrpCat.Colimits.toCocone F f)) _ = _
  rw [hc.fac]
  simp

end

section

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

variable (c : Cocone F)

set_option backward.isDefEq.respectTransparency false in
theorem Quot.desc_toCocone_desc_app [DecidableEq J] {A : Type w} [AddCommGroup A] (f : AddCommGrpCat.Colimits.Quot F →+ A)
    (hc : IsColimit c) (x : AddCommGrpCat.Colimits.Quot F) : hc.desc (AddCommGrpCat.Colimits.toCocone F f) (AddCommGrpCat.Colimits.Quot.desc F c x) = f x := by
  conv_rhs => rw [← AddCommGrpCat.Colimits.Quot.desc_toCocone_desc F c f hc]
  dsimp

end

section

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

variable (c : Cocone F)

set_option backward.isDefEq.respectTransparency false in
theorem Quot.map_ι [DecidableEq J] {j j' : J} {f : j ⟶ j'} (x : F.obj j) :
    AddCommGrpCat.Colimits.Quot.ι F j' (F.map f x) = AddCommGrpCat.Colimits.Quot.ι F j x := by
  dsimp [ι]
  refine eq_of_sub_eq_zero ?_
  erw [← (QuotientAddGroup.mk' (Relations F)).map_sub, ← AddMonoidHom.mem_ker]
  rw [QuotientAddGroup.ker_mk']
  simp only [DFinsupp.singleAddHom_apply]
  exact AddSubgroup.subset_closure ⟨j, j', f, x, rfl⟩

end

section

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

variable (c : Cocone F)

set_option backward.isDefEq.respectTransparency false in
theorem Quot.ι_desc [DecidableEq J] (j : J) (x : F.obj j) :
    AddCommGrpCat.Colimits.Quot.desc F c (AddCommGrpCat.Colimits.Quot.ι F j x) = c.ι.app j x := by
  dsimp [desc, ι]
  erw [QuotientAddGroup.lift_mk']
  simp

end

section

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

theorem hasColimit_of_small_quot [DecidableEq J] (h : Small.{w} (AddCommGrpCat.Colimits.Quot F)) : HasColimit F := ⟨_, AddCommGrpCat.Colimits.colimitCoconeIsColimit F⟩

end

section

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

variable (c : Cocone F)

theorem quotToQuotUlift_ι [DecidableEq J] (j : J) (x : F.obj j) :
    AddCommGrpCat.Colimits.quotToQuotUlift F (AddCommGrpCat.Colimits.Quot.ι F j x) = AddCommGrpCat.Colimits.Quot.ι _ j (ULift.up x) := by
  dsimp [AddCommGrpCat.Colimits.quotToQuotUlift, AddCommGrpCat.Colimits.Quot.ι]
  conv_lhs => erw [AddMonoidHom.comp_apply (QuotientAddGroup.mk' (Relations F))
    (DFinsupp.singleAddHom _ j), QuotientAddGroup.lift_mk']
  simp only [DFinsupp.singleAddHom_apply, DFinsupp.sumAddHom_single, AddMonoidHom.coe_comp,
    AddMonoidHom.coe_coe, Function.comp_apply]
  rfl

end

section

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

variable (c : Cocone F)

set_option backward.isDefEq.respectTransparency false in
theorem quotUliftToQuot_ι [DecidableEq J] (j : J) (x : (F ⋙ uliftFunctor.{u'}).obj j) :
    AddCommGrpCat.Colimits.quotUliftToQuot F (AddCommGrpCat.Colimits.Quot.ι _ j x) = AddCommGrpCat.Colimits.Quot.ι F j x.down := by
  dsimp [AddCommGrpCat.Colimits.quotUliftToQuot, AddCommGrpCat.Colimits.Quot.ι]
  conv_lhs => erw [AddMonoidHom.comp_apply (QuotientAddGroup.mk' (Relations (F ⋙ uliftFunctor)))
    (DFinsupp.singleAddHom _ j), QuotientAddGroup.lift_mk']
  simp only [Functor.comp_obj, uliftFunctor_obj, DFinsupp.singleAddHom_apply,
    DFinsupp.sumAddHom_single, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply]
  rfl

end
