import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem two_le_natDegree_of_nextCoeff_eraseLead (hlead : f.eraseLead ≠ 0)
    (hnext : f.nextCoeff = 0) : 2 ≤ f.natDegree := by
  contrapose! hlead
  rw [Nat.lt_succ_iff, Nat.le_one_iff_eq_zero_or_eq_one, natDegree_eq_zero, natDegree_eq_one]
    at hlead
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, rfl⟩ := hlead
  · simp
  · rw [nextCoeff_C_mul_X_add_C ha] at hnext
    subst b
    simp

