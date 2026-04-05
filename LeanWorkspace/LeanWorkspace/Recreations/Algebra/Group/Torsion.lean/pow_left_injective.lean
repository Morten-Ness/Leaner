import Mathlib

variable {M G : Type*}

variable [Monoid M]

variable [IsMulTorsionFree M] {n : ℕ} {a b : M}

theorem pow_left_injective (hn : n ≠ 0) : Function.Injective fun a : M ↦ a ^ n := IsMulTorsionFree.pow_left_injective hn

