FAIL
import Mathlib

universe uR uS uA uB

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommRing R] [Ring A]

variable [Algebra R A] {s t : Set A}

theorem adjoin_eq_ring_closure (s : Set A) :
    (Algebra.adjoin R s).toSubring = Subring.closure (Set.range (algebraMap R A) ∪ s) := by
  ext x
  constructor
  · intro hx
    refine Subring.closure_le.2 ?_
    intro y hy
    rcases hy with hy | hy
    · rcases hy with ⟨r, rfl⟩
      exact (Algebra.adjoin R s).algebraMap_mem r
    · exact hx
  · intro hx
    refine Subring.closure_induction hx ?hadd ?hmul ?hone ?hneg ?hbase
    · intro a b ha hb
      exact (Algebra.adjoin R s).add_mem ha hb
    · intro a b ha hb
      exact (Algebra.adjoin R s).mul_mem ha hb
    · exact (Algebra.adjoin R s).one_mem
    · intro a ha
      exact (Algebra.adjoin R s).neg_mem ha
    · intro y hy
      rcases hy with hy | hy
      · rcases hy with ⟨r, rfl⟩
        exact (Algebra.adjoin R s).algebraMap_mem r
      · exact Algebra.subset_adjoin hy
