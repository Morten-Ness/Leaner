import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] {a b : R} {m n : ℕ}

theorem nsmul_le {F α : Type*} [AddMonoid α] [FunLike F α R] [ZeroHomClass F α R]
    [NonnegHomClass F α R] {f : F} (hna : IsNonarchimedean f) {n : ℕ} {a : α} :
    f (n • a) ≤ f a := by
  induction n with
  | zero => simp
  | succ n _ =>
    rw [add_nsmul]
    apply le_trans <| hna (n • a) (1 • a)
    simpa

