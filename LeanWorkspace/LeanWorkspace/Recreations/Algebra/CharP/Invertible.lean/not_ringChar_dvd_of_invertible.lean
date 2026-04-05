import Mathlib

variable {R K : Type*}

variable [Ring R] {p : ℕ} [CharP R p]

theorem not_ringChar_dvd_of_invertible {t : ℕ} [Invertible (t : R)] [Nontrivial R] :
    ¬ringChar R ∣ t := by
  rw [← ringChar.spec, ← Ne]
  exact Invertible.ne_zero (t : R)

