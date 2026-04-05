import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem comp_eq : (f ≫ ofHom GrpCat.SurjectiveOfEpiAuxs.g) = f ≫ ofHom GrpCat.SurjectiveOfEpiAuxs.h := by
  ext a
  simp only [hom_comp, hom_ofHom, MonoidHom.coe_comp, Function.comp_apply]
  have : f a ∈ { b | GrpCat.SurjectiveOfEpiAuxs.h b = GrpCat.SurjectiveOfEpiAuxs.g b } := by
    rw [← GrpCat.SurjectiveOfEpiAuxs.agree]
    use a
  rw [this]

