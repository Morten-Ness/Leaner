import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

theorem Algebra.adjoin_nat {R : Type*} [Semiring R] (s : Set R) :
    Algebra.adjoin ℕ s = subalgebraOfSubsemiring (Subsemiring.closure s) := le_antisymm (Algebra.adjoin_le Subsemiring.subset_closure)
    (Subsemiring.closure_le.2 Algebra.subset_adjoin : Subsemiring.closure s ≤ (Algebra.adjoin ℕ s).toSubsemiring)

