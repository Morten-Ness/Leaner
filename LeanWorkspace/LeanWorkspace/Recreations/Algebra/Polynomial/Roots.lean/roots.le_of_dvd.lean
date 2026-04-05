import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots.le_of_dvd (h : q ≠ 0) : p ∣ q → Polynomial.roots p ≤ Polynomial.roots q := by
  rintro ⟨k, rfl⟩
  exact Multiset.le_iff_exists_add.mpr ⟨k.roots, Polynomial.roots_mul h⟩

