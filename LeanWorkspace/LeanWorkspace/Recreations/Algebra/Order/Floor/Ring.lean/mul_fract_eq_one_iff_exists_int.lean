import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] {a b : R}

theorem mul_fract_eq_one_iff_exists_int {x : R} {k : R} (hk : 1 < k) :
    k * fract x = 1 ↔ ∃ n : ℤ, k * x = k * n + 1 := by
  rw [fract, mul_sub, sub_eq_iff_eq_add']
  refine ⟨fun hx ↦ ⟨⌊x⌋, hx⟩, ?_⟩
  rintro ⟨n, hn⟩
  convert hn
  have hk0 : 0 < (k : R) := zero_le_one.trans_lt hk
  rw [Int.floor_eq_iff, ← mul_le_mul_iff_right₀ hk0, ← mul_lt_mul_iff_right₀ hk0, hn]
  simp [mul_add, hk]

