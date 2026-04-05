import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_eq_of_natDegree_le_card_of_ne_zero {S : Finset R}
    (hS : ∀ x ∈ S, p.eval x = 0) (hcard : p.natDegree ≤ S.card) (hp : p ≠ 0) : p.roots = S.val := Polynomial.roots_eq_of_degree_le_card_of_ne_zero hS (degree_le_of_natDegree_le hcard) hp

