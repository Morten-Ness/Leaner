import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem rootMultiplicity_le_rootMultiplicity_of_dvd {p q : R[X]} (hq : q ≠ 0) (hpq : p ∣ q) (x : R) :
    p.rootMultiplicity x ≤ q.rootMultiplicity x := by
  obtain ⟨_, rfl⟩ := hpq
  exact Nat.le_of_add_right_le <| Polynomial.le_rootMultiplicity_mul x hq

