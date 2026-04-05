import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem rootMultiplicity_le_iff (p0 : p ≠ 0) (a : R) (n : ℕ) :
    Polynomial.rootMultiplicity a p ≤ n ↔ ¬(Polynomial.X - Polynomial.C a) ^ (n + 1) ∣ p := by
  rw [← (Polynomial.le_rootMultiplicity_iff p0).not, not_le, Nat.lt_add_one_iff]

