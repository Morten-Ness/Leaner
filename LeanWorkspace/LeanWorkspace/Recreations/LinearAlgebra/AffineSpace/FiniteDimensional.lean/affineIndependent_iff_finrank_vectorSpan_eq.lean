import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

theorem affineIndependent_iff_finrank_vectorSpan_eq [Fintype ι] (p : ι → P) {n : ℕ}
    (hc : Fintype.card ι = n + 1) :
    AffineIndependent k p ↔ finrank k (vectorSpan k (Set.range p)) = n := by
  classical
  have hn : Nonempty ι := by simp [← Fintype.card_pos_iff, hc]
  obtain ⟨i₁⟩ := hn
  rw [affineIndependent_iff_linearIndependent_vsub _ _ i₁,
    linearIndependent_iff_card_eq_finrank_span, eq_comm,
    vectorSpan_range_eq_span_range_vsub_right_ne k p i₁, Set.finrank]
  rw [← Finset.card_univ] at hc
  rw [Fintype.subtype_card]
  simp [Finset.filter_ne', Finset.card_erase_of_mem, hc]

