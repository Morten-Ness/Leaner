import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem map_mem_nthRootsFinset_one {S F : Type*} [CommRing S] [IsDomain S] [FunLike F R S]
    [RingHomClass F R S] {x : R} (hx : x ∈ Polynomial.nthRootsFinset n 1) (f : F) :
    f x ∈ Polynomial.nthRootsFinset n 1 := by
  rw [← (map_one f)]
  exact Polynomial.map_mem_nthRootsFinset hx _

