import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem eval_geom_sum {R} [CommSemiring R] {n : ℕ} {x : R} :
    Polynomial.eval x (∑ i ∈ range n, Polynomial.X ^ i) = ∑ i ∈ range n, x ^ i := by simp [Polynomial.eval_finset_sum]

