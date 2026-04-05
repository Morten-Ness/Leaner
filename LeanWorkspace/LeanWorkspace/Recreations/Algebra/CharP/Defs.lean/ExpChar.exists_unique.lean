import Mathlib

variable (R : Type*)

theorem ExpChar.exists_unique [Ring R] [IsDomain R] : ∃! q, ExpChar R q := let ⟨q, H⟩ := ExpChar.exists R
  ⟨q, H, fun _ H2 ↦ ExpChar.eq H2 H⟩

