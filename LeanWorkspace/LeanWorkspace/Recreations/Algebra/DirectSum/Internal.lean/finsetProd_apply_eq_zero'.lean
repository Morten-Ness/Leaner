import Mathlib

open scoped DirectSum

variable {ι : Type*} {σ S R : Type*}

variable [AddCommMonoid ι] [LinearOrder ι] [IsOrderedAddMonoid ι] [DecidableEq ι]

variable [CanonicallyOrderedAdd ι]

variable [CommSemiring R] [SetLike σ R] [AddSubmonoidClass σ R]

variable {A : ι → σ} [SetLike.GradedMonoid A]

theorem finsetProd_apply_eq_zero' {s : Finset ((⨁ i, A i) × ι)}
    (hs : ∀ xn ∈ s, ∀ k < xn.2, xn.1 k = 0) ⦃n : ι⦄ (hn : n < ∑ xn ∈ s, xn.2) :
    (∏ xn ∈ s, xn.1) n = 0 := by
  simpa using listProd_apply_eq_zero' (l := s.toList) (by simpa using hs) (by simpa)

