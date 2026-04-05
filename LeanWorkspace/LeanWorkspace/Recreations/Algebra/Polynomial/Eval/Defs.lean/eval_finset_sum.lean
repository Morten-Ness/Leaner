import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem eval_finset_sum (s : Finset ι) (g : ι → R[X]) (x : R) :
    (∑ i ∈ s, g i).eval x = ∑ i ∈ s, (g i).eval x := Polynomial.eval₂_finset_sum _ _ _ _

