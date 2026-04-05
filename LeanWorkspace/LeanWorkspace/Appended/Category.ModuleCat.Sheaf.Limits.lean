import Mathlib

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {D : Type u₂} [Category.{v₂} D]

variable {R : Cᵒᵖ ⥤ RingCat.{u}}
  {F : D ⥤ PresheafOfModules.{v} R}
  [∀ X, Small.{v} ((F ⋙ evaluation R X) ⋙ forget _).sections]
  {c : Cone F}
  [HasLimitsOfShape D AddCommGrpCat.{v}]

theorem isSheaf_of_isLimit (hc : IsLimit c) (hF : ∀ j, Presheaf.IsSheaf J (F.obj j).presheaf) :
    Presheaf.IsSheaf J (c.pt.presheaf) := by
  let G : D ⥤ Sheaf J AddCommGrpCat.{v} :=
    { obj := fun j => ⟨(F.obj j).presheaf, hF j⟩
      map := fun φ => ⟨(PresheafOfModules.toPresheaf R).map (F.map φ)⟩ }
  exact Sheaf.isSheaf_of_isLimit G _ (isLimitOfPreserves (toPresheaf R) hc)

end
