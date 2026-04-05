import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem den_dvd_iff {A : Matrix m n ℚ} {r : ℕ} :
    A.den ∣ r ↔ ∀ i j, (A i j).den ∣ r := by
  simp [Matrix.den]

