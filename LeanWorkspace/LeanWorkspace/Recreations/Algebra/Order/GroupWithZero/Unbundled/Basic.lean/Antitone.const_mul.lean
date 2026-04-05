import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

variable [Preorder α] {f g : α → M₀}

theorem Antitone.const_mul [PosMulMono M₀] (hf : Antitone f) (ha : 0 ≤ a) :
    Antitone fun x ↦ a * f x := (monotone_mul_left_of_nonneg ha).comp_antitone hf

