import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [PartialOrder M₀] {a b c d : M₀} {m n : ℕ}

variable [Preorder α] {f g : α → M₀}

theorem StrictMono.mul_const [MulPosStrictMono M₀] (hf : StrictMono f) (ha : 0 < a) :
    StrictMono fun x ↦ f x * a := (strictMono_mul_right_of_pos ha).comp hf

