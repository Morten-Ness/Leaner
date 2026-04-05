import Mathlib

variable {A B : Type*} [MonoidWithZero A] [LinearOrderedCommGroupWithZero B] {f : A →*₀ B}

theorem embedding_unit_pos (a : (MonoidWithZeroHom.ValueGroup₀ f)ˣ) :
    0 < embedding a.1 := by
  conv_lhs => rw [← map_zero f, ← MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀ (0 : A)]
  rw [MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.lt_iff_lt]
  simp

