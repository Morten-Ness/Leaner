import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem eval₂_at_ofNat {S : Type*} [Semiring S] (f : R →+* S) (n : ℕ) [n.AtLeastTwo] :
    p.eval₂ f ofNat(n) = f (p.eval (ofNat(n))) := by
  simp [OfNat.ofNat]

