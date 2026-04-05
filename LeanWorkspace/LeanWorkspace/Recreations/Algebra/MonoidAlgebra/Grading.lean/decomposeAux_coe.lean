import Mathlib

variable {M : Type*} {ι : Type*} {R : Type*}

variable [AddMonoid M] [DecidableEq ι] [AddMonoid ι] [CommSemiring R] (f : M →+ ι)

set_option backward.isDefEq.respectTransparency false in
theorem decomposeAux_coe {i : ι} (x : gradeBy R f i) :
    AddMonoidAlgebra.decomposeAux f ↑x = DirectSum.of (fun i => gradeBy R f i) i x := by
  classical
  obtain ⟨x, hx⟩ := x
  revert hx
  refine Finsupp.induction x ?_ ?_
  · intro hx
    symm
    exact map_zero _
  · intro m b y hmy hb ih hmby
    have : Disjoint (Finsupp.single m b).support y.support := by
      simpa only [Finsupp.support_single_ne_zero _ hb, Finset.disjoint_singleton_left]
    rw [AddMonoidAlgebra.mem_gradeBy_iff, Finsupp.support_add_eq this, Finset.coe_union, Set.union_subset_iff]
      at hmby
    obtain ⟨h1, h2⟩ := hmby
    have : f m = i := by
      rwa [Finsupp.support_single_ne_zero _ hb, Finset.coe_singleton, Set.singleton_subset_iff]
        at h1
    subst this
    simp only [map_add, AddMonoidAlgebra.decomposeAux_single f m]
    let ih' := ih h2
    dsimp at ih'
    rw [ih', ← map_add]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    congr 2

