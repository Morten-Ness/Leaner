import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem div_dvd_of_dvd {p q : R} (hpq : q ∣ p) : p / q ∣ p := by
  rcases hpq with ⟨r, rfl⟩
  by_cases hq : q = 0
  · subst hq
    simp
  · refine ⟨q, ?_⟩
    simp [hq, mul_comm]
