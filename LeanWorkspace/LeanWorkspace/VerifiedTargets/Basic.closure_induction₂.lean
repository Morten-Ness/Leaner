import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem closure_induction₂ {motive : (x y : M) → x ∈ Submonoid.closure s → y ∈ Submonoid.closure s → Prop}
    (mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), motive x y (Submonoid.subset_closure hx) (Submonoid.subset_closure hy))
    (one_left : ∀ x hx, motive 1 x (one_mem _) hx) (one_right : ∀ x hx, motive x 1 hx (one_mem _))
    (mul_left : ∀ x y z hx hy hz,
      motive x z hx hz → motive y z hy hz → motive (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz,
      motive z x hz hx → motive z y hz hy → motive z (x * y) hz (mul_mem hx hy))
    {x y : M} (hx : x ∈ Submonoid.closure s) (hy : y ∈ Submonoid.closure s) : motive x y hx hy := by
  induction hy using Submonoid.closure_induction with
  | mem z hz => induction hx using Submonoid.closure_induction with
    | mem _ h => exact mem _ _ h hz
    | one => exact one_left _ (Submonoid.subset_closure hz)
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
  | one => exact one_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ hx h₁ h₂

