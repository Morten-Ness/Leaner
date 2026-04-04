import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

theorem finrank_vectorSpan_le_iff_not_affineIndependent [Fintype ι] (p : ι → P) {n : ℕ}
    (hc : Fintype.card ι = n + 2) :
    finrank k (vectorSpan k (Set.range p)) ≤ n ↔ ¬AffineIndependent k p := (not_iff_comm.1 (affineIndependent_iff_not_finrank_vectorSpan_le k p hc).symm).symm

