import Mathlib

variable {A : Type u} [Ring A] {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
  [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃]

variable (pres₂ : Presentation.{w₂₀, w₂₁} A M₂) (f : M₁ →ₗ[A] M₂)
  {ι : Type w₁} (g₁ : ι → M₁)

variable {g₁ f} (data : pres₂.CokernelData f g₁)

variable (hg₁ : Submodule.span A (Set.range g₁) = ⊤)

include hg₁ in
theorem isPresentation : (pres₂.cokernelSolution data).IsPresentation := (Module.Presentation.cokernelSolution.isPresentationCore pres₂ data hg₁).isPresentation

