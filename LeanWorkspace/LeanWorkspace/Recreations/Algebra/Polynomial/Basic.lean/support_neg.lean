import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Ring R]

set_option backward.isDefEq.respectTransparency false in
theorem support_neg {p : R[X]} : (-p).support = p.support := by
  rcases p with ⟨⟩
  rw [← Polynomial.ofFinsupp_neg, Polynomial.support, Polynomial.support, Finsupp.support_neg]

