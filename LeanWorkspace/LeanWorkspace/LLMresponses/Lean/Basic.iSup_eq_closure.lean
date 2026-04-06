import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem iSup_eq_closure {ι : Sort*} (p : ι → Submonoid M) :
    ⨆ i, p i = Submonoid.closure (⋃ i, (p i : Set M)) := by
  simpa using Submonoid.iSup_eq_closure p
