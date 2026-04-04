import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

theorem AffineIndependent.card_le_card_of_subset_affineSpan {s t : Finset V}
    (hs : AffineIndependent k ((↑) : s → V)) (hst : (s : Set V) ⊆ affineSpan k (t : Set V)) :
    #s ≤ #t := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht' := t.eq_empty_or_nonempty
  · simpa [Set.subset_empty_iff] using hst
  have := hs'.to_subtype
  have := ht'.to_set.to_subtype
  have direction_le := AffineSubspace.direction_le (affineSpan_mono k hst)
  rw [AffineSubspace.affineSpan_coe, direction_affineSpan, direction_affineSpan,
    ← @Subtype.range_coe _ (s : Set V), ← @Subtype.range_coe _ (t : Set V)] at direction_le
  have finrank_le := add_le_add_left (Submodule.finrank_mono direction_le) 1
  -- We use `erw` to elide the difference between `↥s` and `↥(s : Set V)}`
  erw [hs.finrank_vectorSpan_add_one] at finrank_le
  simpa using finrank_le.trans <| finrank_vectorSpan_range_add_one_le _ _

