import Mathlib

variable {R : Type*} [CommSemiring R] (E : LinearRecurrence R)

theorem is_sol_iff_mem_solSpace (u : ℕ → R) : E.IsSolution u ↔ u ∈ E.solSpace := Iff.rfl

