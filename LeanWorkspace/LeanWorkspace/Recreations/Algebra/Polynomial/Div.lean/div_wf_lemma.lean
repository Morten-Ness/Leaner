import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem div_wf_lemma (h : degree q ≤ degree p ∧ p ≠ 0) (hq : Polynomial.Monic q) :
    degree (p - q * (Polynomial.C (leadingCoeff p) * Polynomial.X ^ (natDegree p - natDegree q))) < degree p := have hp : leadingCoeff p ≠ 0 := mt leadingCoeff_eq_zero.1 h.2
  have hq0 : q ≠ 0 := hq.ne_zero_of_polynomial_ne h.2
  have hlt : natDegree q ≤ natDegree p :=
    (Nat.cast_le (α := WithBot ℕ)).1
      (by rw [← degree_eq_natDegree h.2, ← degree_eq_natDegree hq0]; exact h.1)
  degree_sub_lt
    (by
      rw [hq.degree_mul_comm, hq.degree_mul, degree_C_mul_X_pow _ hp, degree_eq_natDegree h.2,
        degree_eq_natDegree hq0, ← Nat.cast_add, tsub_add_cancel_of_le hlt])
    h.2 (by rw [leadingCoeff_monic_mul hq, leadingCoeff_mul_X_pow, leadingCoeff_C])

