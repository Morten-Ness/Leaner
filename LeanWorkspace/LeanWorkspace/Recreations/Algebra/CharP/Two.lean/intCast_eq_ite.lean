import Mathlib

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem intCast_eq_ite (n : ℤ) : (n : R) = if Even n then 0 else 1 := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simpa using CharTwo.natCast_eq_ite n

