import Mathlib

variable {n' : Type*} [DecidableEq n'] [Fintype n'] {R : Type*} [CommRing R]

theorem zpow_add {A : M} (ha : IsUnit A.det) (m n : ℤ) : A ^ (m + n) = A ^ m * A ^ n := by
  induction n with
  | zero => simp
  | succ n ihn => simp only [← add_assoc, Matrix.zpow_add_one ha, ihn, mul_assoc]
  | pred n ihn => rw [Matrix.zpow_sub_one ha, ← mul_assoc, ← ihn, ← Matrix.zpow_sub_one ha, add_sub_assoc]

