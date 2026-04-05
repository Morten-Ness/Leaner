import Mathlib

variable {R : Type*} [CommSemiring R] (E : LinearRecurrence R)

theorem eq_mk_of_is_sol_of_eq_init' {u : ℕ → R} {init : Fin E.order → R} (h : E.IsSolution u)
    (heq : ∀ n : Fin E.order, u n = init n) : u = E.mkSol init := funext (E.eq_mk_of_is_sol_of_eq_init h heq)

