import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

theorem pow_right_anti₀ [PosMulMono M₀] (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) : Antitone (fun n : ℕ ↦ a ^ n) := antitone_nat_of_succ_le fun n ↦ by
    have : ZeroLEOneClass M₀ := ⟨ha₀.trans ha₁⟩
    rw [← mul_one (a ^ n), pow_succ]
    exact mul_le_mul_of_nonneg_left ha₁ (pow_nonneg ha₀ n)

