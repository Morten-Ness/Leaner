import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem natDegree_ne_zero_induction_on {M : R[X] → Prop} {f : R[X]} (f0 : f.natDegree ≠ 0)
    (h_C_add : ∀ {a p}, M p → M (Polynomial.C a + p)) (h_add : ∀ {p q}, M p → M q → M (p + q))
    (h_monomial : ∀ {n : ℕ} {a : R}, a ≠ 0 → n ≠ 0 → M (monomial n a)) : M f := by
  suffices f.natDegree = 0 ∨ M f from Or.recOn this (fun h => (f0 h).elim) id
  refine Polynomial.induction_on f ?_ ?_ ?_
  · exact fun a => Or.inl (natDegree_C _)
  · rintro p q (hp | hp) (hq | hq)
    · refine Or.inl ?_
      rw [eq_C_of_natDegree_eq_zero hp, eq_C_of_natDegree_eq_zero hq, ← C_add, natDegree_C]
    · refine Or.inr ?_
      rw [eq_C_of_natDegree_eq_zero hp]
      exact h_C_add hq
    · refine Or.inr ?_
      rw [eq_C_of_natDegree_eq_zero hq, add_comm]
      exact h_C_add hp
    · exact Or.inr (h_add hp hq)
  · intro n a _
    by_cases a0 : a = 0
    · exact Or.inl (by rw [a0, C_0, zero_mul, natDegree_zero])
    · refine Or.inr ?_
      rw [C_mul_X_pow_eq_monomial]
      exact h_monomial a0 n.succ_ne_zero

