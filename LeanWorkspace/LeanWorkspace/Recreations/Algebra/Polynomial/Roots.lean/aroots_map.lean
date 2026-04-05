import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem aroots_map (p : T[X]) [CommRing S] [Algebra T S] [Algebra S R] [Algebra T R]
    [IsScalarTower T S R] :
    (p.map (algebraMap T S)).aroots R = p.aroots R := by
  rw [Polynomial.aroots_def, Polynomial.aroots_def, map_map, IsScalarTower.algebraMap_eq T S R]

