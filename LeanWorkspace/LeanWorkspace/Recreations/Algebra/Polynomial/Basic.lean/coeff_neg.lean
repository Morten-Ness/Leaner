import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Ring R]

set_option backward.isDefEq.respectTransparency false in
theorem coeff_neg (p : R[X]) (n : ℕ) : Polynomial.coeff (-p) n = -Polynomial.coeff p n := by
  rcases p with ⟨⟩
  rw [← Polynomial.ofFinsupp_neg, Polynomial.coeff, Polynomial.coeff, Finsupp.neg_apply]

