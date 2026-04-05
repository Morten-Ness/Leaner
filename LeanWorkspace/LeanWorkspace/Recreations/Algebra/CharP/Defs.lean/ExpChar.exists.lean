import Mathlib

variable (R : Type*)

theorem ExpChar.exists [Ring R] [IsDomain R] : ∃ q, ExpChar R q := by
  obtain _ | ⟨p, ⟨hp⟩, _⟩ := CharP.exists' R
  exacts [⟨1, .zero⟩, ⟨p, .prime hp⟩]

