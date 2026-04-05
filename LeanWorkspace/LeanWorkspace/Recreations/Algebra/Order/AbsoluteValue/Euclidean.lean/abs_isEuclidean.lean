import Mathlib

theorem abs_isEuclidean : IsEuclidean (AbsoluteValue.abs : AbsoluteValue ℤ ℤ) := { map_lt_map_iff' := fun {x y} =>
       show abs x < abs y ↔ natAbs x < natAbs y by rw [abs_eq_natAbs, abs_eq_natAbs, ofNat_lt] }

