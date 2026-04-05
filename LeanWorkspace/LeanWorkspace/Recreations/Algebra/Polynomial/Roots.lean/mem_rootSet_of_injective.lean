import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem mem_rootSet_of_injective [CommRing S] {p : S[X]} [Algebra S R]
    (h : Function.Injective (algebraMap S R)) {x : R} (hp : p ≠ 0) :
    x ∈ p.rootSet R ↔ aeval x p = 0 := by
  classical
  exact Multiset.mem_toFinset.trans (Polynomial.mem_roots_map_of_injective h hp)

