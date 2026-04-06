FAIL
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
  let P : M → Prop := fun x =>
    ∀ hx : x ∈ Submonoid.closure s, ∀ y, ∀ hy : y ∈ Submonoid.closure s, motive x y hx hy
  have hP : ∀ x, x ∈ Submonoid.closure s → P x := by
    intro x hxcl
    refine Submonoid.closure_induction hxcl ?_ ?_ ?_
    · intro x hxS
      intro hxcl' y hycl
      refine Submonoid.closure_induction hycl ?_ ?_ ?_
      · intro y hyS
        exact mem x y hxS hyS
      · exact one_right x hxcl'
      · intro y₁ y₂ hy₁ hy₂ ih₁ ih₂
        exact mul_right y₁ y₂ x hy₁ hy₂ hxcl' ih₁ ih₂
    · intro y hycl
      exact one_left y hycl
    · intro x₁ x₂ hx₁ hx₂ ih₁ ih₂
      intro hxcl' y hycl
      exact mul_left x₁ x₂ y hx₁ hx₂ hycl (ih₁ hx₁ hxcl' y hycl) (ih₂ hx₂ hxcl' y hycl)
  exact hP x hx hx y hy
