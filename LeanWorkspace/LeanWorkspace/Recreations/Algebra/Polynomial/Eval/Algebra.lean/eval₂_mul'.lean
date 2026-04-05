import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] [Semiring S] [Algebra R S] (x : S) (p q : R[X])

theorem eval₂_mul' :
    (p * q).eval₂ (algebraMap R S) x = p.eval₂ (algebraMap R S) x * q.eval₂ (algebraMap R S) x := by
  exact eval₂_mul_noncomm _ _ fun k => Algebra.commute_algebraMap_left (coeff q k) x

