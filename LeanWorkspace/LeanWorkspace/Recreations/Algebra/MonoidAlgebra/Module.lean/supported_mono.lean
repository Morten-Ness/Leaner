import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S M : Type*}

variable {S : Type*}

variable [Semiring R] [Semiring S] [Module R S] {s t : Set M} {x : S[M]}

theorem supported_mono (hst : s ⊆ t) : MonoidAlgebra.supported R S s ≤ MonoidAlgebra.supported R S t := fun _ h ↦ h.trans hst

