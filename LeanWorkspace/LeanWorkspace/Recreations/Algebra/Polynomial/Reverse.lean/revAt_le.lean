import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem revAt_le {N i : ℕ} (H : i ≤ N) : Polynomial.revAt N i = N - i := if_pos H

