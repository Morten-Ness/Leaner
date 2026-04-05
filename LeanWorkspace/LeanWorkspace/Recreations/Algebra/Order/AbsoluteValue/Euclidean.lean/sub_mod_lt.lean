import Mathlib

variable {R S : Type*} [EuclideanDomain R] [Semiring S] [PartialOrder S]

variable (abv : AbsoluteValue R S)

theorem sub_mod_lt (h : abv.IsEuclidean) (a : R) {b : R} (hb : b ≠ 0) : abv (a % b) < abv b := AbsoluteValue.IsEuclidean.map_lt_map_iff h.mpr (EuclideanDomain.mod_lt a hb)

