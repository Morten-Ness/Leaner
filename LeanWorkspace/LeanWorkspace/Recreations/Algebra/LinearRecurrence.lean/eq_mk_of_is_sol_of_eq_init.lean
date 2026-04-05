import Mathlib

variable {R : Type*} [CommSemiring R] (E : LinearRecurrence R)

theorem eq_mk_of_is_sol_of_eq_init {u : ℕ → R} {init : Fin E.order → R} (h : E.IsSolution u)
    (heq : ∀ n : Fin E.order, u n = init n) : ∀ n, u n = E.mkSol init n := by
  intro n
  rw [LinearRecurrence.mkSol]
  split_ifs with h'
  · exact mod_cast heq ⟨n, h'⟩
  · dsimp only
    rw [← tsub_add_cancel_of_le (le_of_not_gt h'), h (n - E.order)]
    congr with k
    rw [eq_mk_of_is_sol_of_eq_init h heq (n - E.order + k)]
    simp

