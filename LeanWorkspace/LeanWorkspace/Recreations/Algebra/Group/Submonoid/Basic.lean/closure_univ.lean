import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem closure_univ : Submonoid.closure (Set.univ : Set M) = ⊤ := @coe_top M _ ▸ Submonoid.closure_eq ⊤

