import Mathlib

variable {G M R K : Type*}

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K] {x y ε : K}

variable [ExistsAddOfLE K]

theorem exists_pow_btwn_of_lt_mul {a b c : K} (h : a < b * c) (hb₀ : 0 < b) (hb₁ : b ≤ 1)
    (hc₀ : 0 < c) (hc₁ : c < 1) :
    ∃ n : ℕ, a < c ^ n ∧ c ^ n < b := by
  have := exists_pow_lt_of_lt_one hb₀ hc₁
  refine ⟨Nat.find this, h.trans_le ?_, Nat.find_spec this⟩
  by_contra! H
  have hn : Nat.find this ≠ 0 := by
    intro hf
    simp only [hf, pow_zero] at H
    exact (H.trans <| (mul_lt_of_lt_one_right hb₀ hc₁).trans_le hb₁).false
  rw [(Nat.succ_pred_eq_of_ne_zero hn).symm, pow_succ, mul_lt_mul_iff_left₀ hc₀] at H
  exact Nat.find_min this (Nat.sub_one_lt hn) H

