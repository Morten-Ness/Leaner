import Mathlib

variable {R : Type*} [CommSemiring R] (E : LinearRecurrence R)

theorem is_sol_mkSol (init : Fin E.order → R) : E.IsSolution (E.mkSol init) := by
  intro n
  rw [LinearRecurrence.mkSol]
  simp

