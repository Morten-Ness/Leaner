import Mathlib

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

theorem extendScalars_δ (M₁ M₂ : ModuleCat R) :
    letI := f.toAlgebra
    dsimp% δ (extendScalars f) M₁ M₂ =
      (AlgebraTensorModule.distribBaseChange R S M₁ M₂).toModuleIso.hom :=
  rfl

