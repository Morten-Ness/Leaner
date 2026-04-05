import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem first_contAux_eq_h_one : g.contsAux 1 = ⟨g.h, 1⟩ := rfl

