import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem mem_closure {x : M} : x ∈ Submonoid.closure s ↔ ∀ S : Submonoid M, s ⊆ S → x ∈ S := Submonoid.mem_sInf

