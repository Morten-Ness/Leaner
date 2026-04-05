import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem rootMultiplicity_eq_natFind_of_ne_zero {p : R[X]} (p0 : p ≠ 0) {a : R}
    [DecidablePred fun n : ℕ => ¬(Polynomial.X - Polynomial.C a) ^ (n + 1) ∣ p] :
    Polynomial.rootMultiplicity a p = Nat.find (Polynomial.finiteMultiplicity_X_sub_C a p0) := by
  dsimp [Polynomial.rootMultiplicity]
  rw [dif_neg p0]
  congr

