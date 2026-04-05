import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem eval₂_at_one {S : Type*} [Semiring S] (f : R →+* S) : p.eval₂ f 1 = f (p.eval 1) := by
  convert Polynomial.eval₂_at_apply (p := p) f 1
  simp

