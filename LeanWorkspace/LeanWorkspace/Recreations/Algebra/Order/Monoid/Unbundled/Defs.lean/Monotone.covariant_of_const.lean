import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable {α : Type*} {M N μ} [Preorder α] [Preorder N]

variable {f : N → α}

theorem Monotone.covariant_of_const [CovariantClass M N μ (· ≤ ·)] (hf : Monotone f) (m : M) :
    Monotone (f <| μ m ·) := hf.comp (Covariant.monotone_of_const m)

