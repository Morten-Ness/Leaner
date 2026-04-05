import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem closure_union (s t : Set M) : Subsemigroup.closure (s ∪ t) = Subsemigroup.closure s ⊔ Subsemigroup.closure t := (Subsemigroup.gi M).gc.l_sup

