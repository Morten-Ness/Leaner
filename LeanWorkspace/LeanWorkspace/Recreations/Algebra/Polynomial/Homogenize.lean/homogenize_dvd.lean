import Mathlib

variable {R : Type*} [CommSemiring R]

theorem homogenize_dvd [NoZeroDivisors R] {p q : R[X]} (h : p ∣ q) :
    Polynomial.homogenize p p.natDegree ∣ Polynomial.homogenize q q.natDegree := by
  rcases h with ⟨r, rfl⟩
  obtain rfl | rfl | ⟨hp₀, hr₀⟩ : p = 0 ∨ r = 0 ∨ p ≠ 0 ∧ r ≠ 0 := by tauto
  · simp
  · simp
  · rw [natDegree_mul hp₀ hr₀, Polynomial.homogenize_mul _ _ le_rfl le_rfl]
    apply dvd_mul_right

