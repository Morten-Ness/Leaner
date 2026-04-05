import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

variable (F : C ⥤ D)

variable {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

theorem pushforward_id_comp :
    PresheafOfModules.pushforwardComp.{v} (G := 𝟭 _) φ (𝟙 R) =
      isoWhiskerRight (PresheafOfModules.pushforwardId R) (PresheafOfModules.pushforward.{v} φ) ≪≫ leftUnitor _ := by ext; rfl

