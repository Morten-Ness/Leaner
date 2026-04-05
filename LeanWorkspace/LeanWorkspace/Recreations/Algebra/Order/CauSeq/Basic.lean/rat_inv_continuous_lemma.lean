import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  (abv : β → α) [IsAbsoluteValue abv]

theorem rat_inv_continuous_lemma {β : Type*} [DivisionRing β] (abv : β → α) [IsAbsoluteValue abv]
    {ε K : α} (ε0 : 0 < ε) (K0 : 0 < K) :
    ∃ δ > 0, ∀ {a b : β}, K ≤ abv a → K ≤ abv b → abv (a - b) < δ → abv (a⁻¹ - b⁻¹) < ε := by
  refine ⟨K * ε * K, mul_pos (mul_pos K0 ε0) K0, fun {a b} ha hb h => ?_⟩
  have a0 := K0.trans_le ha
  have b0 := K0.trans_le hb
  rw [inv_sub_inv' ((abv_pos abv).1 a0) ((abv_pos abv).1 b0), abv_mul abv, abv_mul abv, abv_inv abv,
    abv_inv abv, abv_sub abv]
  refine lt_of_mul_lt_mul_left (lt_of_mul_lt_mul_right ?_ b0.le) a0.le
  rw [mul_assoc, inv_mul_cancel_right₀ b0.ne', ← mul_assoc, mul_inv_cancel₀ a0.ne', one_mul]
  refine h.trans_le ?_
  gcongr
  exact mul_nonneg a0.le ε0.le

