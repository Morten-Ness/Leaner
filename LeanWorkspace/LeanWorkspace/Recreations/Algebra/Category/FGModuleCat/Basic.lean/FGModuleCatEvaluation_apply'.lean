import Mathlib

variable (K : Type u) [Field K]

variable (V W : FGModuleCat K)

set_option backward.isDefEq.respectTransparency false in
theorem FGModuleCatEvaluation_apply' (f : FGModuleCat.FGModuleCatDual K V) (x : V) :
    DFunLike.coe
      (F := ((ModuleCat.of K (Module.Dual K V) ⊗ V.obj).carrier →ₗ[K] (𝟙_ (ModuleCat K))))
      (FGModuleCat.FGModuleCatEvaluation K V).hom.hom (f ⊗ₜ x) = f.toFun x :=
  contractLeft_apply f x

