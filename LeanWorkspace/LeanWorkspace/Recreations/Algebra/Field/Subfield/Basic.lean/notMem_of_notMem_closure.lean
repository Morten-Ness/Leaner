import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem notMem_of_notMem_closure {s : Set K} {P : K} (hP : P ∉ Subfield.closure s) : P ∉ s := fun h =>
  hP (Subfield.subset_closure h)

