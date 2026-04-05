import Mathlib

variable {u v : ℤ}

theorem isUnit_iff_natAbs_eq : IsUnit u ↔ u.natAbs = 1 := by simp [natAbs_eq_iff, Int.isUnit_iff]

alias ⟨IsUnit.natAbs_eq, _⟩ := isUnit_iff_natAbs_eq

