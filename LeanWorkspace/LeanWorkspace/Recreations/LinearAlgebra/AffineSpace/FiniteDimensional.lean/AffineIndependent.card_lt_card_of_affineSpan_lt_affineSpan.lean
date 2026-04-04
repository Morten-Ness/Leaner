import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

theorem AffineIndependent.card_lt_card_of_affineSpan_lt_affineSpan {s t : Finset V}
    (hs : AffineIndependent k ((↑) : s → V))
    (hst : affineSpan k (s : Set V) < affineSpan k (t : Set V)) : #s < #t := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simpa [card_pos] using hst
  obtain rfl | ht' := t.eq_empty_or_nonempty
  · simp at hst
  have := hs'.to_subtype
  have := ht'.to_set.to_subtype
  have dir_lt := AffineSubspace.direction_lt_of_nonempty (k := k) hst <| hs'.to_set.affineSpan k
  rw [direction_affineSpan, direction_affineSpan,
    ← @Subtype.range_coe _ (s : Set V), ← @Subtype.range_coe _ (t : Set V)] at dir_lt
  have finrank_lt := add_lt_add_left (Submodule.finrank_lt_finrank_of_lt dir_lt) 1
  -- We use `erw` to elide the difference between `↥s` and `↥(s : Set V)}`
  erw [hs.finrank_vectorSpan_add_one] at finrank_lt
  simpa using finrank_lt.trans_le <| finrank_vectorSpan_range_add_one_le _ _

