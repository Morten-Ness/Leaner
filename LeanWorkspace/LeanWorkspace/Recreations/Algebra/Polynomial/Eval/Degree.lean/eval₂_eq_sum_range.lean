import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S] (f : R →+* S) (x : S)

theorem eval₂_eq_sum_range :
    p.eval₂ f x = ∑ i ∈ Finset.range (p.natDegree + 1), f (p.coeff i) * x ^ i := _root_.trans (congr_arg _ p.as_sum_range)
    (_root_.trans (eval₂_finset_sum f _ _ x) (congr_arg _ (by simp)))

