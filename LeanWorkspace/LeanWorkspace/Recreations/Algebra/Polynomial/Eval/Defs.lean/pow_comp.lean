import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem pow_comp {R : Type*} [CommSemiring R] (p q : R[X]) (n : ℕ) :
    (p ^ n).comp q = p.comp q ^ n := (MonoidHom.mk (OneHom.mk (fun r : R[X] => r.comp q) Polynomial.one_comp) fun r s => Polynomial.mul_comp r s q).map_pow
    p n

