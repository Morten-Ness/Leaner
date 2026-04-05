import Mathlib

variable (R : Type u) [Semiring R]

theorem coe_basisMonomials : (Polynomial.basisMonomials R : ℕ → R[X]) = fun s => monomial s 1 := funext fun _ => ofFinsupp_single _ _

