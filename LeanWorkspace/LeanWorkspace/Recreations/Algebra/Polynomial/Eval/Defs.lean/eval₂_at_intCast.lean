import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Ring R] {p q r : R[X]}

theorem eval₂_at_intCast {S : Type*} [Ring S] (f : R →+* S) (n : ℤ) :
    p.eval₂ f n = f (p.eval n) := by
  convert Polynomial.eval₂_at_apply (p := p) f n
  simp

