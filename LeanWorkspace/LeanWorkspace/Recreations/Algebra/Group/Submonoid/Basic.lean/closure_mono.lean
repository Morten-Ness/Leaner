import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem closure_mono ⦃s t : Set M⦄ (h : s ⊆ t) : Submonoid.closure s ≤ Submonoid.closure t := Submonoid.closure_le.2 <| Subset.trans h Submonoid.subset_closure

