import Mathlib

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

theorem IsUnit.intrinsicStar {f : WithConv (Module.End R E)} (hf : IsUnit f.ofConv) :
    IsUnit (star f).ofConv := by
  have ⟨u, hu⟩ := hf
  have : IsUnit (star (toConv (u : Module.End R E))).ofConv := (star (toConv u)).ofConv.isUnit
  simpa [hu] using this

