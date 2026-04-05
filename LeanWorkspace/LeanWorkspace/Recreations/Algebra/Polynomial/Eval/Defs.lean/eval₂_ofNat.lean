import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S) (x : S)

theorem eval₂_ofNat {S : Type*} [Semiring S] (n : ℕ) [n.AtLeastTwo] (f : R →+* S) (a : S) :
    (ofNat(n) : R[X]).eval₂ f a = ofNat(n) := by
  simp [OfNat.ofNat]

