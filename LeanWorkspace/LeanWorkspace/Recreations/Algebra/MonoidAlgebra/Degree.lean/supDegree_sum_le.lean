import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [SemilatticeSup B] [OrderBot B] (D : A → B)

theorem supDegree_sum_le {ι} {s : Finset ι} {f : ι → R[A]} :
    (∑ i ∈ s, f i).supDegree D ≤ s.sup (fun i => (f i).supDegree D) := by
  classical
  exact (Finset.sup_mono Finsupp.support_finset_sum).trans_eq (Finset.sup_biUnion _ _)

