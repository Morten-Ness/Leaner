import Mathlib

variable {u v : ℤ}

theorem isUnit_mul_self (hu : IsUnit u) : u * u = 1 := (Int.isUnit_eq_one_or hu).elim (fun h ↦ h.symm ▸ rfl) fun h ↦ h.symm ▸ rfl

