import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem zeroth_contAux_eq_one_zero : g.contsAux 0 = ⟨1, 0⟩ := rfl

