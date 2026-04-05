import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

set_option backward.isDefEq.respectTransparency false in
theorem monomial_left_inj {a : R} (ha : a ≠ 0) {i j : ℕ} :
    Polynomial.monomial i a = Polynomial.monomial j a ↔ i = j := by
  simp only [← Polynomial.ofFinsupp_single, ofFinsupp.injEq, Finsupp.single_left_inj ha]

