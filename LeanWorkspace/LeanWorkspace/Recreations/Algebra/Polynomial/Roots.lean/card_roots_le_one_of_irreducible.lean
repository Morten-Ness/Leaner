import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem card_roots_le_one_of_irreducible (hirr : Irreducible p) : p.roots.card ≤ 1 := by
  obtain hp | ⟨x, hx⟩ := p.roots.empty_or_exists_mem
  · simp [hp]
  convert Polynomial.card_roots' p
  exact (natDegree_eq_of_degree_eq_some <| degree_eq_one_of_irreducible_of_root hirr <|
    Polynomial.isRoot_of_mem_roots hx).symm

