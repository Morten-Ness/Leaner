import Mathlib

variable {M₀ G₀ : Type*}

variable {R S : Type*} {x y : R}

theorem exists_isNilpotent_of_not_isReduced {R : Type*} [Zero R] [Pow R ℕ] (h : ¬IsReduced R) :
    ∃ x : R, x ≠ 0 ∧ IsNilpotent x := by
  simpa [isReduced_iff, not_forall, and_comm] using h

