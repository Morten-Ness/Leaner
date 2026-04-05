import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem exists_max_root [LinearOrder R] (p : R[X]) (hp : p ≠ 0) : ∃ x₀, ∀ x, p.IsRoot x → x ≤ x₀ := Set.exists_upper_bound_image _ _ <| Polynomial.finite_setOf_isRoot hp

