import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem dense_induction {motive : M → Prop} (s : Set M) (Submonoid.closure : Submonoid.closure s = ⊤)
    (mem : ∀ x ∈ s, motive x) (one : motive 1) (mul : ∀ x y, motive x → motive y → motive (x * y))
    (x : M) : motive x := by
  induction Submonoid.closure.symm ▸ mem_top x using Submonoid.closure_induction with
  | mem _ h => exact mem _ h
  | one => exact one
  | mul _ _ _ _ h₁ h₂ => exact mul _ _ h₁ h₂

