import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem induction_on {motive : R[X] → Prop} (p : R[X]) (Polynomial.C : ∀ a, motive (Polynomial.C a))
    (add : ∀ p q, motive p → motive q → motive (p + q))
    (Polynomial.monomial : ∀ (n : ℕ) (a : R),
      motive (Polynomial.C a * Polynomial.X ^ n) → motive (Polynomial.C a * Polynomial.X ^ (n + 1))) : motive p := by
  have A : ∀ {n : ℕ} {a}, motive (Polynomial.C a * Polynomial.X ^ n) := by
    intro n a
    induction n with
    | zero => rw [pow_zero, mul_one]; exact Polynomial.C a
    | succ n ih => exact Polynomial.monomial _ _ ih
  have B : ∀ s : Finset ℕ, motive (s.sum fun n : ℕ => Polynomial.C (p.coeff n) * Polynomial.X ^ n) := by
    apply Finset.induction
    · convert Polynomial.C 0
      exact Polynomial.C_0.symm
    · intro n s ns ih
      rw [Finset.sum_insert ns]
      exact add _ _ A ih
  rw [← Polynomial.sum_C_mul_X_pow_eq p, Polynomial.sum]
  exact B (Polynomial.support p)

