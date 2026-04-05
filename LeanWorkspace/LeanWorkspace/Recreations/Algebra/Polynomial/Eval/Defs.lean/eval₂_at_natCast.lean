import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem eval₂_at_natCast {S : Type*} [Semiring S] (f : R →+* S) (n : ℕ) :
    p.eval₂ f n = f (p.eval n) := by
  convert Polynomial.eval₂_at_apply (p := p) f n
  simp

