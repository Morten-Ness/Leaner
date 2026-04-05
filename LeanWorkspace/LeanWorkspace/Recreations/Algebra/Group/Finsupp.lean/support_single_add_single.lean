import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem support_single_add_single [DecidableEq ι] {f₁ f₂ : ι} {g₁ g₂ : M}
    (H : f₁ ≠ f₂) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) :
    (single f₁ g₁ + single f₂ g₂).support = {f₁, f₂} := by
  rw [Finsupp.support_add_eq, support_single_ne_zero _ hg₁, support_single_ne_zero _ hg₂]
  · simp
  · simp [support_single_ne_zero, *]

