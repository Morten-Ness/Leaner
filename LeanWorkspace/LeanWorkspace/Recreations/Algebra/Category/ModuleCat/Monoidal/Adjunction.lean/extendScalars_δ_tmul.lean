import Mathlib

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

theorem extendScalars_δ_tmul (M₁ M₂ : ModuleCat R) (m₁ : M₁) (m₂ : M₂) :
    letI := f.toAlgebra
    dsimp% δ (extendScalars f) M₁ M₂ (((1 : S) ⊗ₜ[R] (m₁ ⊗ₜ[R] m₂) :)) =
      ((1 : S) ⊗ₜ[R] m₁) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m₂) := rfl

noncomputable instance : (restrictScalars f).LaxMonoidal :=
  (extendRestrictScalarsAdj f).rightAdjointLaxMonoidal

