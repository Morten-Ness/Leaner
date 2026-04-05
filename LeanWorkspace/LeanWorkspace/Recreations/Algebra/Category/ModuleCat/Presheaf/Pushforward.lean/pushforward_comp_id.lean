import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

variable (F : C ⥤ D)

variable {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

theorem pushforward_comp_id :
    PresheafOfModules.pushforwardComp.{v} (F := 𝟭 C) (𝟙 S) φ =
      isoWhiskerLeft (PresheafOfModules.pushforward.{v} φ) (PresheafOfModules.pushforwardId S) ≪≫ rightUnitor _ := by ext; rfl

