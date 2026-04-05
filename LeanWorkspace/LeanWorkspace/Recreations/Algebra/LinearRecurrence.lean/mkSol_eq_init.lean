import Mathlib

variable {R : Type*} [CommSemiring R] (E : LinearRecurrence R)

theorem mkSol_eq_init (init : Fin E.order → R) : ∀ n : Fin E.order, E.mkSol init n = init n := by
  intro n
  rw [LinearRecurrence.mkSol]
  simp only [n.is_lt, dif_pos, Fin.mk_val]

