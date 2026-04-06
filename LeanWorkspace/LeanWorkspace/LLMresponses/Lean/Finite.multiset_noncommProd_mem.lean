FAIL
import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem multiset_noncommProd_mem (K : Subgroup G) (g : Multiset G) (comm) :
    (∀ a ∈ g, a ∈ K) → g.noncommProd comm ∈ K := by
  intro hg
  classical
  rw [Multiset.noncommProd_eq_foldr]
  refine Subgroup.pow_induction_on_right ?_ K.one_mem ?_
  · intro a ha
    exact hg a ha
  · intro a b ha hb
    exact K.mul_mem ha hb
