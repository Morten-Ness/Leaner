import Mathlib

open scoped DirectSum

variable {ι : Type*} {σ S R : Type*}

variable [AddCommMonoid ι] [LinearOrder ι] [IsOrderedAddMonoid ι] [DecidableEq ι]

variable [CanonicallyOrderedAdd ι]

variable [CommSemiring R] [SetLike σ R] [AddSubmonoidClass σ R]

variable {A : ι → σ} [SetLike.GradedMonoid A]

theorem multisetProd_apply_eq_zero' {s : Multiset ((⨁ i, A i) × ι)}
    (hs : ∀ xn ∈ s, ∀ k < xn.2, xn.1 k = 0) ⦃n : ι⦄ (hn : n < (s.map Prod.snd).sum) :
    (s.map Prod.fst).prod n = 0 := by
  have := listProd_apply_eq_zero' (l := s.toList) (by simpa using hs)
    (by simpa [← Multiset.sum_coe, ← Multiset.map_coe])
  simpa [← Multiset.prod_coe, ← Multiset.map_coe]

