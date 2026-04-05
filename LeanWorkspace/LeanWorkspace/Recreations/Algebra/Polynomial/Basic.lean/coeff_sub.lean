import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Ring R]

set_option backward.isDefEq.respectTransparency false in
theorem coeff_sub (p q : R[X]) (n : ℕ) : Polynomial.coeff (p - q) n = Polynomial.coeff p n - Polynomial.coeff q n := by
  rcases p with ⟨⟩
  rcases q with ⟨⟩
  rw [← Polynomial.ofFinsupp_sub, Polynomial.coeff, Polynomial.coeff, Polynomial.coeff, Finsupp.sub_apply]

