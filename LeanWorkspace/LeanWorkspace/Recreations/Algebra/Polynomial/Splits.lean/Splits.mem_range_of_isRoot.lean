import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem Splits.mem_range_of_isRoot {S : Type*} [CommRing S] [IsDomain S] [IsSimpleRing R]
    (hf : f.Splits) (hf0 : f ≠ 0) {i : R →+* S} {x : S} (hx : (f.map i).IsRoot x) :
    x ∈ i.range := by
  rw [← mem_roots (map_ne_zero hf0), hf.roots_map, Multiset.mem_map] at hx
  obtain ⟨x, -, hx⟩ := hx
  exact ⟨x, hx⟩

