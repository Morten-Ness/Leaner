import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degrees_add_of_disjoint [DecidableEq σ] (h : Disjoint p.degrees q.degrees) :
    (p + q).degrees = p.degrees ∪ q.degrees := MvPolynomial.degrees_add_le.antisymm <| Multiset.union_le (MvPolynomial.le_degrees_add_left h) (MvPolynomial.le_degrees_add_right h)

