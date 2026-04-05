import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem closure_iUnion {ι} (s : ι → Set M) : Submonoid.closure (⋃ i, s i) = ⨆ i, Submonoid.closure (s i) := (Submonoid.gi M).gc.l_iSup

