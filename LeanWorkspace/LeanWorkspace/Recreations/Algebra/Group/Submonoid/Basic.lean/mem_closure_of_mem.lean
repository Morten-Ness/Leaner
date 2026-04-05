import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem mem_closure_of_mem {s : Set M} {x : M} (hx : x ∈ s) : x ∈ Submonoid.closure s := Submonoid.subset_closure hx

