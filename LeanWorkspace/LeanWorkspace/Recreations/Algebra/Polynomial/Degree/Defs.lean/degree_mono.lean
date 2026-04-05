import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_mono [Semiring S] {f : R[X]} {g : S[X]} (h : f.support ⊆ g.support) :
    f.degree ≤ g.degree := Finset.sup_mono h

