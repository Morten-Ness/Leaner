import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

variable [Fintype m] [DecidableEq m]

theorem trace_conj' {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) :
    trace (M⁻¹ * N * M) = trace N := by rw [← h.unit_spec, ← Matrix.coe_units_inv, trace_units_conj']

