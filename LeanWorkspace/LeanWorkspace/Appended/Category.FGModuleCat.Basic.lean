import Mathlib

section

variable (K : Type u) [Field K]

variable (V W : FGModuleCat K)

set_option backward.isDefEq.respectTransparency false in
theorem FGModuleCatEvaluation_apply' (f : FGModuleCat.FGModuleCatDual K V) (x : V) :
    DFunLike.coe
      (F := ((ModuleCat.of K (Module.Dual K V) ⊗ V.obj).carrier →ₗ[K] (𝟙_ (ModuleCat K))))
      (FGModuleCat.FGModuleCatEvaluation K V).hom.hom (f ⊗ₜ x) = f.toFun x :=
  contractLeft_apply f x

end

section

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


theorem LinearMap.comp_id_fgModuleCat
    {R} [Ring R] {G : FGModuleCat.{v} R} {H : Type v} [AddCommGroup H] [Module R H]
    (f : G →ₗ[R] H) : f.comp (ModuleCat.Hom.hom (InducedCategory.Hom.hom (𝟙 G))) = f := ModuleCat.hom_ext_iff.mp <| Category.id_comp (ModuleCat.ofHom f)

#adaptation_note /-- After https://github.com/leanprover/lean4/pull/12179
the simpNF linter complains about this being `@[simp]`. -/

end

section

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

end
