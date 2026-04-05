import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem closure_empty : Submonoid.closure (∅ : Set M) = ⊥ := (Submonoid.gi M).gc.l_bot

