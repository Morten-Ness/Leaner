import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] [FloorRing k] {b : k}

theorem fract_div_intCast_eq_div_intCast_mod {m : ℤ} {n : ℕ} :
    fract ((m : k) / n) = ↑(m % n) / n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  replace hn : 0 < (n : k) := by norm_cast
  have : ∀ {l : ℤ}, 0 ≤ l → fract ((l : k) / n) = ↑(l % n) / n := by
    intro l hl
    obtain ⟨l₀, rfl | rfl⟩ := l.eq_nat_or_neg
    · rw [cast_natCast, ← natCast_mod, cast_natCast, Int.fract_div_natCast_eq_div_natCast_mod]
    · rw [Right.nonneg_neg_iff, natCast_nonpos_iff] at hl
      simp [hl]
  obtain ⟨m₀, rfl | rfl⟩ := m.eq_nat_or_neg
  · exact this (natCast_nonneg m₀)
  let q := ⌈↑m₀ / (n : k)⌉
  let m₁ := q * ↑n - (↑m₀ : ℤ)
  have hm₁ : 0 ≤ m₁ := by
    simpa [m₁, ← @cast_le k, ← div_le_iff₀ hn] using FloorRing.gc_ceil_coe.le_u_l _
  calc
    fract ((Int.cast (-(m₀ : ℤ)) : k) / (n : k))
      = fract (-(m₀ : k) / n) := by simp
    _ = fract ((m₁ : k) / n) := ?_
    _ = Int.cast (m₁ % (n : ℤ)) / Nat.cast n := this hm₁
    _ = Int.cast (-(↑m₀ : ℤ) % ↑n) / Nat.cast n := ?_
  · rw [← Int.fract_intCast_add q, ← mul_div_cancel_right₀ (q : k) hn.ne', ← add_div, ← sub_eq_add_neg]
    simp [m₁]
  · congr 2
    simp only [m₁]
    rw [sub_eq_add_neg, add_comm (q * ↑n), add_mul_emod_self_right]

