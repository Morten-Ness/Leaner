import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem mem_rootSet_of_ne {p : T[X]} {S : Type*} [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] (hp : p ≠ 0) {a : S} : a ∈ p.rootSet S ↔ aeval a p = 0 := Polynomial.mem_rootSet.trans <| and_iff_right hp

