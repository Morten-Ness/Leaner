import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_eq_zero_of_irreducible_of_natDegree_ne_one (hirr : Irreducible p)
    (hdeg : p.natDegree ≠ 1) : p.roots = 0 := by
  by_contra hroots
  have ⟨x, hx⟩ := exists_mem_of_ne_zero hroots
  exact hdeg <| natDegree_eq_of_degree_eq_some <|
    degree_eq_one_of_irreducible_of_root hirr (Polynomial.mem_roots'.mp hx).right

