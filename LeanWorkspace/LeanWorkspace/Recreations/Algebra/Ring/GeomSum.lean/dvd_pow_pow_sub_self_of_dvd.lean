import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R}

theorem dvd_pow_pow_sub_self_of_dvd {r : R} {p a b : ℕ} (h : a ∣ b) :
    r ^ p ^ a - r ∣ r ^ p ^ b - r := by
  by_cases hp₀ : p = 0
  · by_cases hb₀ : b = 0
    · rw [hp₀, hb₀, pow_zero, pow_one, sub_self]
      exact dvd_zero _
    have ha₀ : a ≠ 0 := by rintro rfl; rw [zero_dvd_iff] at h; tauto
    rw [hp₀, zero_pow ha₀, zero_pow hb₀]
  have hp (c) : 1 ≤ p ^ c := Nat.pow_pos <| pos_of_ne_zero hp₀
  rw [← Nat.sub_add_cancel (hp a), ← Nat.sub_add_cancel (hp b), pow_succ', pow_succ',
    ← mul_sub_one, ← mul_sub_one]
  refine mul_dvd_mul_left _ <| dvd_pow_sub_one_of_dvd <| Int.natCast_dvd_natCast.mp ?_
  rw [Nat.cast_sub (hp a), Nat.cast_sub (hp b), Nat.cast_pow, Nat.cast_pow]
  exact dvd_pow_sub_one_of_dvd h

