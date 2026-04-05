import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem zeroth_den_eq_one : g.dens 0 = 1 := rfl

