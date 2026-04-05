import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] {a b : R} {m n : ℕ}

theorem nmul_le {F α : Type*} [NonAssocSemiring α] [FunLike F α R] [ZeroHomClass F α R]
    [NonnegHomClass F α R] {f : F} (hna : IsNonarchimedean f) {n : ℕ} {a : α} :
    f (n * a) ≤ f a := by
  rw [← nsmul_eq_mul]
  exact IsNonarchimedean.nsmul_le hna

