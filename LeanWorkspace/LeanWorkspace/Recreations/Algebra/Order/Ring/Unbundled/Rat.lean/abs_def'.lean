import Mathlib

variable {a b c p q : ℚ}

theorem abs_def' (q : ℚ) :
    |q| = ⟨|q.num|, q.den, q.den_ne_zero, q.num.abs_eq_natAbs ▸ q.reduced⟩ := by
  refine ext ?_ ?_ <;>
    simp [Int.abs_eq_natAbs, Rat.abs_def,
      ← Rat.mk_eq_divInt (num := q.num.natAbs) (nz := q.den_ne_zero) (c := q.reduced)]

