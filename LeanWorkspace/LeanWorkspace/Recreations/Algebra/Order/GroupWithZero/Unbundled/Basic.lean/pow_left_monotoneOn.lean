import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

theorem pow_left_monotoneOn [PosMulMono M₀] [MulPosMono M₀] :
    MonotoneOn (fun a : M₀ ↦ a ^ n) {x | 0 ≤ x} := fun _a ha _b _ hab ↦ pow_le_pow_left₀ ha hab _

