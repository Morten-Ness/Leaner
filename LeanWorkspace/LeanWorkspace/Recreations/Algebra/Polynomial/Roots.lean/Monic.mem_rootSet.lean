import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem Monic.mem_rootSet {p : T[X]} (hp : Monic p) {S : Type*} [CommRing S] [IsDomain S]
    [Algebra T S] {a : S} : a ∈ p.rootSet S ↔ aeval a p = 0 := by
  simp [Polynomial.mem_rootSet', (hp.map (algebraMap T S)).ne_zero]

