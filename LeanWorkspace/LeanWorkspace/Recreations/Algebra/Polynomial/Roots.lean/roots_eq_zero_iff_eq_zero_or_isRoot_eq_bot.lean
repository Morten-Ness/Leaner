import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_eq_zero_iff_eq_zero_or_isRoot_eq_bot : p.roots = 0 ↔ p = 0 ∨ p.IsRoot = ⊥ := by
  rcases eq_or_ne p 0 with rfl | hp0; · simp
  simp [Polynomial.roots_eq_zero_iff_isRoot_eq_bot hp0, hp0]

