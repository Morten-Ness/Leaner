import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable (solution : relations.Solution M)

theorem isPresentation_iff :
    solution.IsPresentation ↔
      Submodule.span A (Set.range solution.var) = ⊤ ∧
      LinearMap.ker solution.π = Submodule.span A (Set.range relations.relation) := by
  rw [← Module.Relations.Solution.injective_fromQuotient_iff_ker_π_eq_span,
    ← Module.Relations.Solution.surjective_π_iff_span_eq_top, ← Module.Relations.Solution.surjective_fromQuotient_iff_surjective_π, ]
  exact ⟨fun h ↦ ⟨h.bijective.2, h.bijective.1⟩, fun h ↦ ⟨⟨h.2, h.1⟩⟩⟩

