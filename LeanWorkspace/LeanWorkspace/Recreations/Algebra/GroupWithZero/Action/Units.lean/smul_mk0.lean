import Mathlib

variable {G₀ G M α β : Type*}

variable [GroupWithZero G₀]

theorem smul_mk0 {α : Type*} [SMul G₀ α] {g : G₀} (hg : g ≠ 0) (a : α) : mk0 g hg • a = g • a := rfl

