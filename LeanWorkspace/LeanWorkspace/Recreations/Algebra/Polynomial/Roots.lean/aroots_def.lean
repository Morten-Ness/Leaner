import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem aroots_def (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] :
    p.aroots S = (p.map (algebraMap T S)).roots := rfl

