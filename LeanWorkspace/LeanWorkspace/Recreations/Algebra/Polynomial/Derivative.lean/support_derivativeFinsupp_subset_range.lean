import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem support_derivativeFinsupp_subset_range {p : R[X]} {n : ℕ} (h : p.natDegree < n) :
    (Polynomial.derivativeFinsupp p).support ⊆ range n := by
  dsimp [Polynomial.derivativeFinsupp]
  exact Finsupp.support_onFinset_subset.trans (Finset.range_subset_range.mpr h)

