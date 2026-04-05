import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

variable [IsDomain R]

theorem _root_.Irreducible.isRoot_eq_bot_of_natDegree_ne_one
    (hi : Irreducible p) (hdeg : p.natDegree ≠ 1) : p.IsRoot = ⊥ := le_bot_iff.mp fun _ ↦ hi.not_isRoot_of_natDegree_ne_one hdeg

