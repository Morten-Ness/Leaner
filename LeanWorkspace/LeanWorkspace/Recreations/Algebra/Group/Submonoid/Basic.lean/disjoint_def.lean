import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem disjoint_def {p₁ p₂ : Submonoid M} :
    Disjoint p₁ p₂ ↔ ∀ {x : M}, x ∈ p₁ → x ∈ p₂ → x = 1 := by
  simp_rw [disjoint_iff_inf_le, SetLike.le_def, mem_inf, and_imp, mem_bot]

