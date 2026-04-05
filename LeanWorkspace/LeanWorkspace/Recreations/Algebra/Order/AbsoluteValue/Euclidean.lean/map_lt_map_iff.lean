import Mathlib

variable {R S : Type*} [EuclideanDomain R] [Semiring S] [PartialOrder S]

variable (abv : AbsoluteValue R S)

theorem map_lt_map_iff {x y : R} (h : abv.IsEuclidean) : abv x < abv y ↔ x ≺ y := map_lt_map_iff' h

attribute [simp] map_lt_map_iff

