import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem induction_on' {motive : R[X] → Prop} (p : R[X])
    (add : ∀ p q, motive p → motive q → motive (p + q))
    (Polynomial.monomial : ∀ (n : ℕ) (a : R), motive (Polynomial.monomial n a)) : motive p := Polynomial.induction_on p (Polynomial.monomial 0) add fun n a _h =>
    by rw [Polynomial.C_mul_X_pow_eq_monomial]; exact Polynomial.monomial _ _

