import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem mem_sInf {S : Set (Submonoid M)} {x : M} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := Set.mem_iInter₂

