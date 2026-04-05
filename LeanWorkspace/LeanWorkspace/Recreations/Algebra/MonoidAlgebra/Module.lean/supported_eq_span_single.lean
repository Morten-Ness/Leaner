import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S M : Type*}

variable {S : Type*}

variable [Semiring R] [Semiring S] [Module R S] {s t : Set M} {x : S[M]}

theorem supported_eq_span_single : MonoidAlgebra.supported R R s = .span R ((fun m ↦ single m 1) '' s) := by
  simp [MonoidAlgebra.supported_eq_map, Finsupp.supported_eq_span_single R s, Submodule.map_span,
    ← Set.image_comp, ofCoeff]

