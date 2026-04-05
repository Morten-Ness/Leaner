import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

omit [IsDomain R] in
theorem Splits.image_rootSet [IsSimpleRing A] (hf : (f.map (algebraMap R A)).Splits)
    (g : A →ₐ[R] B) : g '' f.rootSet A = f.rootSet B := by
  classical
  rw [rootSet, ← Finset.coe_image, ← Multiset.toFinset_map, ← g.coe_toRingHom,
    ← hf.roots_map, map_map, g.comp_algebraMap, ← rootSet]

