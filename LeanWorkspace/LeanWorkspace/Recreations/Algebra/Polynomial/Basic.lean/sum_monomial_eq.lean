import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem sum_monomial_eq : ∀ p : R[X], (p.sum fun n a => Polynomial.monomial n a) = p
  | ⟨_p⟩ => (Polynomial.ofFinsupp_sum _ _).symm.trans (congr_arg _ <| Finsupp.sum_single _)
