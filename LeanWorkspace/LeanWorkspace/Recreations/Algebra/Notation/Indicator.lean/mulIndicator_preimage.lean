import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_preimage (s : Set α) (f : α → M) (B : Set M) :
    Set.mulIndicator s f ⁻¹' B = s.ite (f ⁻¹' B) (1 ⁻¹' B) := letI := Classical.decPred (· ∈ s)
  piecewise_preimage s f 1 B

