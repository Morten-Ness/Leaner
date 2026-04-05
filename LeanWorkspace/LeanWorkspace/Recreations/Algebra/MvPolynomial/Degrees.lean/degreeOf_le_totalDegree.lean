import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degreeOf_le_totalDegree (f : MvPolynomial σ R) (i : σ) : f.degreeOf i ≤ f.totalDegree := MvPolynomial.degreeOf_le_iff.mpr fun d hd ↦ (eq_or_ne (d i) 0).elim (by lia) fun h ↦
    (Finset.single_le_sum (by lia) <| Finsupp.mem_support_iff.mpr h).trans
    (MvPolynomial.le_totalDegree hd)

