import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ Submonoid.closure s) : Submonoid.closure s = S := le_antisymm (Submonoid.closure_le.2 h₁) h₂

