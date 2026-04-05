import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

theorem Algebra.adjoin_int {R : Type*} [Ring R] (s : Set R) :
    Algebra.adjoin ℤ s = subalgebraOfSubring (Subring.closure s) := le_antisymm (Algebra.adjoin_le Subring.subset_closure)
    (Subring.closure_le.2 Algebra.subset_adjoin : Subring.closure s ≤ (Algebra.adjoin ℤ s).toSubring)

