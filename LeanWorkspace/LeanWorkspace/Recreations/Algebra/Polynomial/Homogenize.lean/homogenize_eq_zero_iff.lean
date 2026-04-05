import Mathlib

variable {R : Type*} [CommSemiring R]

theorem homogenize_eq_zero_iff {p : R[X]} {n : ℕ} (hn : p.natDegree ≤ n) :
    p.homogenize n = 0 ↔ p = 0 := ⟨Polynomial.eq_zero_of_homogenize_eq_zero hn, by simp +contextual⟩

