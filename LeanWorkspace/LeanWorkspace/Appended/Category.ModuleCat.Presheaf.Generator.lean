import Mathlib

section

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

set_option backward.isDefEq.respectTransparency false in
theorem freeYonedaEquiv_symm_app (M : PresheafOfModules.{v} R) (X : C)
    (x : M.obj (Opposite.op X)) :
    (PresheafOfModules.freeYonedaEquiv.symm x).app (Opposite.op X) (ModuleCat.freeMk (𝟙 _)) = x := by
  dsimp [PresheafOfModules.freeYonedaEquiv, freeHomEquiv, yonedaEquiv]
  rw [ModuleCat.freeDesc_apply, op_id, M.presheaf.map_id]
  rfl

end

section

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

variable {C : Type u} [SmallCategory.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R)

set_option backward.isDefEq.respectTransparency false in
theorem fromFreeYonedaCoproduct_app_mk (m : M.Elements) :
    M.fromFreeYonedaCoproduct.app _ (M.freeYonedaCoproductMk m) = m.2 := by
  dsimp [PresheafOfModules.freeYonedaCoproductMk]
  erw [M.ι_fromFreeYonedaCoproduct_apply m]
  rw [PresheafOfModules.Elements.fromFreeYoneda_app_apply m]

end

section

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}} {M : PresheafOfModules.{v} R}

theorem fromFreeYoneda_app_apply (m : M.Elements) :
    m.fromFreeYoneda.app m.1 (ModuleCat.freeMk (𝟙 _)) = m.2 := by
  apply PresheafOfModules.freeYonedaEquiv_symm_app

end

section

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

theorem isDetecting : ObjectProperty.IsDetecting (PresheafOfModules.freeYoneda R) := (PresheafOfModules.freeYoneda.isSeparating R).isDetecting

end

section

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

theorem isSeparating : ObjectProperty.IsSeparating (PresheafOfModules.freeYoneda R) := by
  intro M N f₁ f₂ h
  ext ⟨X⟩ m
  obtain ⟨g, rfl⟩ := PresheafOfModules.freeYonedaEquiv.surjective m
  exact congr_arg PresheafOfModules.freeYonedaEquiv (h _ ⟨X⟩ g)

end

section

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

variable {C : Type u} [SmallCategory.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R)

theorem toFreeYonedaCoproduct_fromFreeYonedaCoproduct :
    M.toFreeYonedaCoproduct ≫ M.fromFreeYonedaCoproduct = 0 := by
  simp [PresheafOfModules.toFreeYonedaCoproduct]

end

section

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

variable {C : Type u} [SmallCategory.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R)

theorem ι_fromFreeYonedaCoproduct_apply (m : M.Elements) (X : Cᵒᵖ) (x : m.freeYoneda.obj X) :
    M.fromFreeYonedaCoproduct.app X ((M.ιFreeYonedaCoproduct m).app X x) =
      m.fromFreeYoneda.app X x := congr_fun ((evaluation R X ⋙ forget _).congr_map (M.ι_fromFreeYonedaCoproduct m)) x

end
