import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem coeff_mul_degree_add_degree (p q : R[X]) :
    coeff (p * q) (natDegree p + natDegree q) = leadingCoeff p * leadingCoeff q := calc
    coeff (p * q) (natDegree p + natDegree q) =
        ∑ x ∈ antidiagonal (natDegree p + natDegree q), coeff p x.1 * coeff q x.2 :=
      coeff_mul _ _ _
    _ = coeff p (natDegree p) * coeff q (natDegree q) := by
      refine Finset.sum_eq_single (natDegree p, natDegree q) ?_ ?_
      · rintro ⟨i, j⟩ h₁ h₂
        rw [mem_antidiagonal] at h₁
        by_cases H : natDegree p < i
        · rw [Polynomial.coeff_eq_zero_of_degree_lt
              (lt_of_le_of_lt Polynomial.degree_le_natDegree (WithBot.coe_lt_coe.2 H)),
            zero_mul]
        · rw [not_lt_iff_eq_or_lt] at H
          rcases H with H | H
          · simp_all
          · suffices natDegree q < j by
              rw [Polynomial.coeff_eq_zero_of_degree_lt
                  (lt_of_le_of_lt Polynomial.degree_le_natDegree (WithBot.coe_lt_coe.2 this)),
                mul_zero]
            by_contra! H'
            exact
              ne_of_lt (Nat.lt_of_lt_of_le (Nat.add_lt_add_right H j) (Nat.add_le_add_left H' _))
                h₁
      · intro H
        exfalso
        apply H
        rw [mem_antidiagonal]

