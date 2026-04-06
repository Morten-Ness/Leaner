import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (S : Type*) [SetLike S K] [h : SubfieldClass S K]

variable {S} {x : K}

theorem ofScientific_mem (s : S) {b : Bool} {n m : ℕ} :
    (OfScientific.ofScientific n b m : K) ∈ s := by
  simpa using SubfieldClass.ofScientific_mem (s := s) (n := n) (b := b) (m := m)
