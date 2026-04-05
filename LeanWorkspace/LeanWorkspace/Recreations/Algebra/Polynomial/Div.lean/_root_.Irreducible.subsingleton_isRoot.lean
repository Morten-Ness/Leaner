import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

variable [IsDomain R]

theorem _root_.Irreducible.subsingleton_isRoot [IsLeftCancelMulZero R]
    (hi : Irreducible p) : { x | p.IsRoot x }.Subsingleton := fun _ hx ↦ (subsingleton_isRoot_of_natDegree_eq_one <| natDegree_eq_of_degree_eq_some <|
    Polynomial.degree_eq_one_of_irreducible_of_root hi hx) hx

