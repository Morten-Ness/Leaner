import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem subset_closure : s ⊆ Submonoid.closure s := fun _ hx => Submonoid.mem_closure.2 fun _ hS => hS hx

