import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem closure_union (s t : Set M) : Submonoid.closure (s ∪ t) = Submonoid.closure s ⊔ Submonoid.closure t := (Submonoid.gi M).gc.l_sup

