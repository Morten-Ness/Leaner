import Mathlib

variable {ι κ α β : Type*} [CommMonoid β]

theorem mulIndicator_biUnion (s : Finset ι) (t : ι → Set κ) {f : κ → β}
    (hs : (s : Set ι).PairwiseDisjoint t) :
    mulIndicator (⋃ i ∈ s, t i) f = fun a ↦ ∏ i ∈ s, mulIndicator (t i) f a := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    ext j
    rw [coe_cons, Set.pairwiseDisjoint_insert_of_notMem (Finset.mem_coe.not.2 hi)] at hs
    classical
    rw [prod_cons, cons_eq_insert, set_biUnion_insert, mulIndicator_union_of_notMem_inter, ih hs.1]
    exact (Set.disjoint_iff.mp (Set.disjoint_iUnion₂_right.mpr hs.2) ·)

