import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable {α : Type*} {M N μ} [Preorder α] [Preorder N]

variable {f : N → α}

theorem Antitone.covariant_of_const [CovariantClass M N μ (· ≤ ·)] (hf : Antitone f) (m : M) :
    Antitone (f <| μ m ·) := hf.comp_monotone <| Covariant.monotone_of_const m

