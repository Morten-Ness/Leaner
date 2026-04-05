import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem closure_le : Submonoid.closure s ≤ S ↔ s ⊆ S := ⟨Subset.trans Submonoid.subset_closure, fun h => sInf_le h⟩

