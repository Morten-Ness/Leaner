import Mathlib

variable {R : Type*}

variable [Semiring R] {p q : SkewPolynomial R}

variable {S S₁ S₂ : Type*}

theorem support_add : (p + q).support ⊆ p.support ∪ q.support := by
  simpa [SkewPolynomial.support, ← Finset.map_union, Finset.map_subset_map] using SkewMonoidAlgebra.support_add

