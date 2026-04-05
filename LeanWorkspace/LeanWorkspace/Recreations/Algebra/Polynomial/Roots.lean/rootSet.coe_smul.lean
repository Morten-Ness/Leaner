import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem rootSet.coe_smul [CommRing S] [Algebra S R] {G : Type*}
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R] {f : S[X]}
    (g : G) (x : f.rootSet R) : (g • x : f.rootSet R) = g • (x : R) := rfl

