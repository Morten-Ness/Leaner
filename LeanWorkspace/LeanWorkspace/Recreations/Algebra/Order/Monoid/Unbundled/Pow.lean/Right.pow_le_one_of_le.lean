import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [Preorder M]

variable [MulRightMono M] {x : M}

theorem Right.pow_le_one_of_le (hx : x ≤ 1) {n : ℕ} : x ^ n ≤ 1 := Right.one_le_pow_of_le (M := Mᵒᵈ) hx

