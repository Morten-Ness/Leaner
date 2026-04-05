import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem mem_roots (hp : p ≠ 0) : a ∈ p.roots ↔ IsRoot p a := Polynomial.mem_roots'.trans <| and_iff_right hp

