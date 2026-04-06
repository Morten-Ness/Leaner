import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem mem_iSup {ι : Sort*} (p : ι → Submonoid M) {m : M} :
    (m ∈ ⨆ i, p i) ↔ ∀ N, (∀ i, p i ≤ N) → m ∈ N := by
  constructor
  · intro hm N hN
    exact show m ∈ N from (iSup_le hN) hm
  · intro h
    exact h (⨆ i, p i) (by
      intro i
      exact le_iSup p i)
