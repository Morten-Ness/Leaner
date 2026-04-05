import Mathlib

variable {R ι : Type*}

variable [AddMonoidWithOne R]

variable [CharP R 2]

theorem natCast_eq_ite (n : ℕ) : (n : R) = if Even n then 0 else 1 := by
  induction n <;> aesop (add simp [one_add_one_eq_two])

