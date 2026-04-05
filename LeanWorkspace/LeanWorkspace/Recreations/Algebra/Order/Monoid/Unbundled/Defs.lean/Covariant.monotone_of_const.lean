import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable {α : Type*} {M N μ} [Preorder α] [Preorder N]

variable {f : N → α}

theorem Covariant.monotone_of_const [CovariantClass M N μ (· ≤ ·)] (m : M) : Monotone (μ m) := fun _ _ ↦ CovariantClass.elim m

