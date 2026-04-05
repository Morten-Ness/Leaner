import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem eval_smul [SMulZeroClass S R] [IsScalarTower S R R] (s : S) (p : R[X])
    (x : R) : (s • p).eval x = s • p.eval x := by
  rw [← smul_one_smul R s p, eval, Polynomial.eval₂_smul, RingHom.id_apply, smul_one_mul, eval₂_id]

