import Mathlib

open scoped Polynomial

variable {n : Type*} [DecidableEq n] [Fintype n]

theorem ZMod.trace_pow_card {p : ℕ} [Fact p.Prime] (M : Matrix n n (ZMod p)) :
    Matrix.trace (M ^ p) = Matrix.trace M ^ p := by have h := FiniteField.trace_pow_card M; rwa [ZMod.card] at h

