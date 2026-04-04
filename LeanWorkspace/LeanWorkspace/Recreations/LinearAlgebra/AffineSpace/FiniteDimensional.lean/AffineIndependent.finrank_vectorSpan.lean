import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

theorem AffineIndependent.finrank_vectorSpan [Fintype ι] {p : ι → P} (hi : AffineIndependent k p)
    {n : ℕ} (hc : Fintype.card ι = n + 1) : finrank k (vectorSpan k (Set.range p)) = n := by
  classical
  rw [← Finset.card_univ] at hc
  rw [← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image]
  exact hi.finrank_vectorSpan_image_finset hc

