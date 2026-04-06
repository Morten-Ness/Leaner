import Mathlib

variable {u v : ℤ}

theorem isUnit_iff : IsUnit u ↔ u = 1 ∨ u = -1 := by
  constructor
  · rintro ⟨a, rfl⟩
    rcases Int.units_eq_one_or a with h | h
    · left
      simpa using congrArg (fun x : ℤˣ => (x : ℤ)) h
    · right
      simpa using congrArg (fun x : ℤˣ => (x : ℤ)) h
  · rintro (rfl | rfl)
    · exact isUnit_one
    · refine ⟨-1, rfl⟩
