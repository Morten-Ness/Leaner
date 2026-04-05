import Mathlib

variable {A : Type u} [CommRing A] {M₁ : Type v₁} {M₂ : Type v₂}
  [AddCommGroup M₁] [AddCommGroup M₂] [Module A M₁] [Module A M₂]

variable (relations₁ : Relations.{w₁₀, w₁₁} A) (relations₂ : Relations.{w₂₀, w₂₁} A)

variable {relations₁ relations₂} (solution₁ : relations₁.Solution M₁)
  (solution₂ : relations₂.Solution M₂)

variable {solution₁ solution₂} (h₁ : solution₁.IsPresentation) (h₂ : solution₂.IsPresentation)

include h₁ h₂ in
theorem IsPresentation.tensor : (solution₁.tensor solution₂).IsPresentation := (Module.Relations.Solution.isPresentationCoreTensor h₁ h₂).isPresentation

