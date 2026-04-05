import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

omit [IsDomain R] in
theorem Splits.image_rootSet_of_map_ne_zero (hf : (f.map (algebraMap R A)).Splits)
    (φ : A →ₐ[R] B) (hφ : f.map (algebraMap R B) ≠ 0) : φ '' f.rootSet A = f.rootSet B := by
  classical
  replace hφ : (f.map (algebraMap R A)).map (φ : A →+* B) ≠ 0 := by
    rwa [map_map, φ.comp_algebraMap]
  replace hf := hf.roots_map_of_ne_zero hφ
  rw [map_map, φ.comp_algebraMap] at hf
  simp [rootSet, aroots, hf, Multiset.toFinset_map]

