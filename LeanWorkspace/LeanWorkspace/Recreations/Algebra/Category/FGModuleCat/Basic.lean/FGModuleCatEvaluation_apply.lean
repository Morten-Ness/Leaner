import Mathlib

variable (K : Type u) [Field K]

variable (V W : FGModuleCat K)

theorem FGModuleCatEvaluation_apply (f : FGModuleCat.FGModuleCatDual K V) (x : V) :
    (FGModuleCat.FGModuleCatEvaluation K V).hom (f ⊗ₜ x) = f.toFun x := contractLeft_apply f x

