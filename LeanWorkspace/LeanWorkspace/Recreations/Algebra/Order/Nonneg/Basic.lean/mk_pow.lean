import Mathlib

variable {α : Type*}

variable [MonoidWithZero α] [Preorder α] [ZeroLEOneClass α] [PosMulMono α]

theorem mk_pow {x : α} (hx : 0 ≤ x) (n : ℕ) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) ^ n = ⟨x ^ n, pow_nonneg hx n⟩ := rfl

