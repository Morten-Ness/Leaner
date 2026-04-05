import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S) (x : S)

variable [Semiring T]

theorem eval₂_finset_sum (s : Finset ι) (g : ι → R[X]) (x : S) :
    (∑ i ∈ s, g i).eval₂ f x = ∑ i ∈ s, (g i).eval₂ f x := map_sum (Polynomial.eval₂AddMonoidHom f x) _ _

