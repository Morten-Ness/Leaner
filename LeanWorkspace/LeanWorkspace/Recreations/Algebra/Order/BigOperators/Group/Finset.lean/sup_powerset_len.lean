import Mathlib

variable {ι α β M N G k R : Type*}

theorem sup_powerset_len [DecidableEq α] (x : Multiset α) :
    (Finset.sup (Finset.range (card x + 1)) fun k => x.powersetCard k) = x.powerset := by
  convert bind_powerset_len x using 1
  rw [Multiset.bind, Multiset.join, ← Finset.range_val, ← Finset.sum_eq_multiset_sum]
  exact
    Eq.symm (Multiset.finset_sum_eq_sup_iff_disjoint.mpr fun _ _ _ _ h => pairwise_disjoint_powersetCard x h)

