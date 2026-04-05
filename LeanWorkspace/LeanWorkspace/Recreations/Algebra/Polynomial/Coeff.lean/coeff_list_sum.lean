import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_list_sum (l : List R[X]) (n : ℕ) :
    l.sum.coeff n = (l.map (Polynomial.lcoeff R n)).sum := map_list_sum (Polynomial.lcoeff R n) _

