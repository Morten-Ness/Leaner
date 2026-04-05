import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

set_option backward.isDefEq.respectTransparency false in
theorem monomial_eq_monomial_iff {m n : ℕ} {a b : R} :
    Polynomial.monomial m a = Polynomial.monomial n b ↔ m = n ∧ a = b ∨ a = 0 ∧ b = 0 := by
  rw [← Polynomial.toFinsupp_inj, Polynomial.toFinsupp_monomial, Polynomial.toFinsupp_monomial, Finsupp.single_eq_single_iff]

