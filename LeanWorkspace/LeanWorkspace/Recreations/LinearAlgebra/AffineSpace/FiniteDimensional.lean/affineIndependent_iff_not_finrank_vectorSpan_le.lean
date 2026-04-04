import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

theorem affineIndependent_iff_not_finrank_vectorSpan_le [Fintype ι] (p : ι → P) {n : ℕ}
    (hc : Fintype.card ι = n + 2) :
    AffineIndependent k p ↔ ¬finrank k (vectorSpan k (Set.range p)) ≤ n := by
  rw [affineIndependent_iff_le_finrank_vectorSpan k p hc, ← Nat.lt_iff_add_one_le, lt_iff_not_ge]

