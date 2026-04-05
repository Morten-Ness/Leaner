import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] {a b : R} {m n : ℕ}

theorem apply_natCast_le_one_of_isNonarchimedean {F α : Type*} [AddMonoidWithOne α] [FunLike F α R]
    [ZeroHomClass F α R] [NonnegHomClass F α R] [OneHomClass F α R] {f : F}
    (hna : IsNonarchimedean f) {n : ℕ} : f n ≤ 1 := by
  rw [← nsmul_one n, ← map_one f]
  exact IsNonarchimedean.nsmul_le hna

