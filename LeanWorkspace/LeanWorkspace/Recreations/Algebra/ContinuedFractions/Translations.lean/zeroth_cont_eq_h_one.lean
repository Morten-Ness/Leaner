import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem zeroth_cont_eq_h_one : g.conts 0 = ⟨g.h, 1⟩ := rfl

