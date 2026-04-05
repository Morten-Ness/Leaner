import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

theorem span_top : span K (span ℤ (Set.range b) : Set E) = ⊤ := by simp [span_span_of_tower]

