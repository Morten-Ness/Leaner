import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable {solution : relations.Solution M}

theorem isPresentation {solution : relations.Solution M}
    (h : Module.Relations.Solution.IsPresentationCore.{max u v w₀} solution) :
    solution.IsPresentation where
  bijective := by
    let e : relations.Quotient ≃ₗ[A] M :=
      LinearEquiv.ofLinear solution.fromQuotient
      ((Module.Relations.Solution.IsPresentationCore.down.{v} h).desc (Module.Relations.Solution.ofQuotient relations))
      (Module.Relations.Solution.IsPresentation.postcomp_injective (Module.Relations.Solution.IsPresentationCore.down.{max u w₀} h) (by aesop)) (by aesop)
    exact e.bijective

