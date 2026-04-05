import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable {α : Type*} {M N μ} [Preorder α] [Preorder N]

variable {f : N → α}

theorem Monotone.covariant_of_const' {μ : N → N → N} [CovariantClass N N (swap μ) (· ≤ ·)]
    (hf : Monotone f) (m : N) : Monotone (f <| μ · m) := Monotone.covariant_of_const (μ := swap μ) hf m

