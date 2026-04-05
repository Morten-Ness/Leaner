import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

variable [IsDomain R]

theorem _root_.Irreducible.not_isRoot_of_natDegree_ne_one
    (hi : Irreducible p) (hdeg : p.natDegree ≠ 1) {x : R} : ¬p.IsRoot x := fun hr ↦ hdeg <| natDegree_eq_of_degree_eq_some <| Polynomial.degree_eq_one_of_irreducible_of_root hi hr

