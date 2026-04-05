import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem revAt_add {N O n o : ℕ} (hn : n ≤ N) (ho : o ≤ O) :
    Polynomial.revAt (N + O) (n + o) = Polynomial.revAt N n + Polynomial.revAt O o := by
  rcases Nat.le.dest hn with ⟨n', rfl⟩
  rcases Nat.le.dest ho with ⟨o', rfl⟩
  repeat' rw [Polynomial.revAt_le (le_add_right rfl.le)]
  rw [add_assoc, add_left_comm n' o, ← add_assoc, Polynomial.revAt_le (le_add_right rfl.le)]
  repeat' rw [add_tsub_cancel_left]

