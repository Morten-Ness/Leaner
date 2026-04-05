import Mathlib

theorem aeval_coe_eq_smeval {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] [Algebra R S]
    (x : S) : ⇑(aeval x) = fun (p : R[X]) => p.smeval x := funext fun p => Polynomial.aeval_eq_smeval x p

