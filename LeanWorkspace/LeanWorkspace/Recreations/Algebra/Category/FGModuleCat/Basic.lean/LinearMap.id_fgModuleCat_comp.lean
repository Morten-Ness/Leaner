import Mathlib

set_option backward.privateInPublic true in
private theorem coevaluation_evaluation :
    letI V' : FGModuleCat K := FGModuleCat.FGModuleCatDual K V
    V' ◁ FGModuleCat.FGModuleCatCoevaluation K V ≫ (α_ V' V V').inv ≫ FGModuleCat.FGModuleCatEvaluation K V ▷ V' =
      (ρ_ V').hom ≫ (λ_ V').inv := by
  ext : 1
  apply contractLeft_assoc_coevaluation K V


set_option backward.privateInPublic true in
private theorem evaluation_coevaluation :
    FGModuleCat.FGModuleCatCoevaluation K V ▷ V ≫
        (α_ V (FGModuleCat.FGModuleCatDual K V) V).hom ≫ V ◁ FGModuleCat.FGModuleCatEvaluation K V =
      (λ_ V).hom ≫ (ρ_ V).inv := by
  ext : 1
  apply contractLeft_assoc_coevaluation' K V


theorem LinearMap.id_fgModuleCat_comp
    {R} [Ring R] {G : Type v} [AddCommGroup G] [Module R G] {H : FGModuleCat.{v} R}
    (f : G →ₗ[R] H) : LinearMap.comp (ModuleCat.Hom.hom (InducedCategory.Hom.hom (𝟙 H))) f = f := ModuleCat.hom_ext_iff.mp <| Category.comp_id (ModuleCat.ofHom f)

