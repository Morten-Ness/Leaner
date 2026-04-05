import Mathlib

section

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

end

section

variable {ι κ α β : Type*} [CommMonoid β]

theorem mulIndicator_biUnion_apply (s : Finset ι) (t : ι → Set κ) {f : κ → β}
    (h : (s : Set ι).PairwiseDisjoint t) (x : κ) :
    mulIndicator (⋃ i ∈ s, t i) f x = ∏ i ∈ s, mulIndicator (t i) f x := by
  rw [Finset.mulIndicator_biUnion s t h]

end

section

variable {ι κ α β : Type*} [CommMonoid β]

theorem prod_mulIndicator_eq_prod_filter (s : Finset ι) (f : ι → κ → β) (t : ι → Set κ) (g : ι → κ)
    [DecidablePred fun i ↦ g i ∈ t i] :
    ∏ i ∈ s, mulIndicator (t i) (f i) (g i) = ∏ i ∈ s with g i ∈ t i, f i (g i) := by
  refine (prod_filter_mul_prod_filter_not s (fun i ↦ g i ∈ t i) _).symm.trans <|
     Eq.trans (congr_arg₂ (· * ·) ?_ ?_) (mul_one _)
  · exact prod_congr rfl fun x hx ↦ mulIndicator_of_mem (mem_filter.1 hx).2 _
  · exact prod_eq_one fun x hx ↦ mulIndicator_of_notMem (mem_filter.1 hx).2 _

end

section

variable {ι κ α β : Type*} [CommMonoid β]

theorem prod_mulIndicator_eq_prod_inter [DecidableEq ι] (s t : Finset ι) (f : ι → β) :
    ∏ i ∈ s, (t : Set ι).mulIndicator f i = ∏ i ∈ s ∩ t, f i := by
  rw [← filter_mem_eq_inter, Finset.prod_mulIndicator_eq_prod_filter]; rfl

end

section

variable {ι κ α β : Type*} [CommMonoid β]

theorem prod_mulIndicator_subset (f : ι → β) {s t : Finset ι} (h : s ⊆ t) :
    ∏ i ∈ t, mulIndicator (↑s) f i = ∏ i ∈ s, f i := Finset.prod_mulIndicator_subset_of_eq_one _ (fun _ ↦ id) h fun _ ↦ rfl

end

section

variable {ι κ α β : Type*} [CommMonoid β]

theorem prod_mulIndicator_subset_of_eq_one [One α] (f : ι → α) (g : ι → α → β) {s t : Finset ι}
    (h : s ⊆ t) (hg : ∀ a, g a 1 = 1) :
    ∏ i ∈ t, g i (mulIndicator ↑s f i) = ∏ i ∈ s, g i (f i) := by
  calc
    _ = ∏ i ∈ s, g i (mulIndicator ↑s f i) := by rw [prod_subset h fun i _ hn ↦ by simp [hn, hg]]
    _ = _ := prod_congr rfl fun i hi ↦ congr_arg _ <| mulIndicator_of_mem hi f

end
