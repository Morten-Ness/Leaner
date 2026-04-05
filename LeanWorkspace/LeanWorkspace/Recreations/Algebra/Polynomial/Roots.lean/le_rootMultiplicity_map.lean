import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable {A B : Type*} [CommRing A] [CommRing B]

theorem le_rootMultiplicity_map {p : A[X]} {f : A →+* B} (hmap : map f p ≠ 0) (a : A) :
    rootMultiplicity a p ≤ rootMultiplicity (f a) (p.map f) := by
  rw [le_rootMultiplicity_iff hmap]
  refine _root_.trans ?_ (_root_.map_dvd (mapRingHom f) (pow_rootMultiplicity_dvd p a))
  rw [map_pow, map_sub, coe_mapRingHom, map_X, map_C]

