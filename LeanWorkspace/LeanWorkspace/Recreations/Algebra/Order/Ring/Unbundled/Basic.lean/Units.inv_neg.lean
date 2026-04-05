import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem Units.inv_neg
    [ZeroLEOneClass R] [NeZero (1 : R)] [MulPosMono R] [PosMulMono R]
    {u : Rˣ} : ↑u⁻¹ < (0 : R) ↔ ↑u < (0 : R) := have : ∀ {u : Rˣ}, ↑u < (0 : R) → ↑u⁻¹ < (0 : R) := @fun u h =>
    neg_of_mul_pos_right (u.mul_inv.symm ▸ zero_lt_one) h.le
  ⟨this, this⟩

