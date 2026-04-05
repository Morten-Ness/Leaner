import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem closure_univ : Subsemigroup.closure (Set.univ : Set M) = ⊤ := @coe_top M _ ▸ Subsemigroup.closure_eq ⊤

