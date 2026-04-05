import Mathlib

open scoped Polynomial

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable {S : Type*} [Semiring S]

theorem natDegree_multiset_sum_le (l : Multiset S[X]) :
    natDegree l.sum ≤ (l.map natDegree).foldr max 0 := Quotient.inductionOn l (by simpa using Polynomial.natDegree_list_sum_le)

