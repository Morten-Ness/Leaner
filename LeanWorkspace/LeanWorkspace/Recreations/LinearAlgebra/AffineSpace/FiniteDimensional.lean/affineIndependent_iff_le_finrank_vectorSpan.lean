import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

theorem affineIndependent_iff_le_finrank_vectorSpan [Fintype ι] (p : ι → P) {n : ℕ}
    (hc : Fintype.card ι = n + 1) :
    AffineIndependent k p ↔ n ≤ finrank k (vectorSpan k (Set.range p)) := by
  rw [affineIndependent_iff_finrank_vectorSpan_eq k p hc]
  constructor
  · rintro rfl
    rfl
  · exact fun hle => le_antisymm (finrank_vectorSpan_range_le k p hc) hle

