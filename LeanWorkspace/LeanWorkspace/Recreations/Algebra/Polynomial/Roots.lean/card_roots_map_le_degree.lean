import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable {A B : Type*} [CommRing A] [CommRing B]

theorem card_roots_map_le_degree {A B : Type*} [Semiring A] [CommRing B] [IsDomain B]
    {f : A →+* B} (p : A[X]) (hp0 : p ≠ 0) : (p.map f).roots.card ≤ p.degree := by
  by_cases hpm0 : p.map f = 0
  · simp [hp0, hpm0, zero_le_degree_iff]
  exact Polynomial.card_roots hpm0 |>.trans degree_map_le

