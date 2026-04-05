import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem Units.inv_pos
    [ZeroLEOneClass R] [NeZero (1 : R)] [PosMulStrictMono R]
    {u : Rˣ} : (0 : R) < ↑u⁻¹ ↔ (0 : R) < u := have : ∀ {u : Rˣ}, (0 : R) < u → (0 : R) < ↑u⁻¹ := @fun u h =>
    (mul_pos_iff_of_pos_left h).mp <| u.mul_inv.symm ▸ zero_lt_one
  ⟨this, this⟩

