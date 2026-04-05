import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem evalRingHom_zero : evalRingHom 0 = constantCoeff := DFunLike.ext _ _ fun p => Polynomial.coeff_zero_eq_eval_zero p.symm

