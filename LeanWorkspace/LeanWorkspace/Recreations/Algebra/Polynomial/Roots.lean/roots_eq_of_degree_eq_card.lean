import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_eq_of_degree_eq_card {S : Finset R}
    (hS : ∀ x ∈ S, p.eval x = 0) (hcard : S.card = p.degree) : p.roots = S.val := Polynomial.roots_eq_of_degree_le_card_of_ne_zero hS (by grind) (by contrapose! hcard; simp [hcard])

