import Mathlib

variable {k : Type*} {V : Type*} {P : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

theorem finrank_vectorSpan_insert_le (s : AffineSubspace k P) (p : P) :
    finrank k (vectorSpan k (insert p (s : Set P))) ≤ finrank k s.direction + 1 := by
  by_cases hf : FiniteDimensional k s.direction; swap
  · have hf' : ¬FiniteDimensional k (vectorSpan k (insert p (s : Set P))) := by
      intro h
      have h' : s.direction ≤ vectorSpan k (insert p (s : Set P)) := by
        conv_lhs => rw [← affineSpan_coe s, direction_affineSpan]
        exact vectorSpan_mono k (Set.subset_insert _ _)
      exact hf (Submodule.finiteDimensional_of_le h')
    rw [finrank_of_infinite_dimensional hf, finrank_of_infinite_dimensional hf', zero_add]
    exact zero_le_one
  rw [← direction_affineSpan, ← affineSpan_insert_affineSpan]
  rcases (s : Set P).eq_empty_or_nonempty with (hs | ⟨p₀, hp₀⟩)
  · rw [coe_eq_bot_iff] at hs
    rw [hs, bot_coe, span_empty, bot_coe, direction_affineSpan, direction_bot, finrank_bot,
      zero_add]
    convert zero_le_one' ℕ
    rw [← finrank_bot k V]
    convert rfl <;> simp
  · rw [affineSpan_coe, direction_affineSpan_insert hp₀, add_comm]
    refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
    gcongr
    refine finrank_le_one ⟨p -ᵥ p₀, Submodule.mem_span_singleton_self _⟩ fun v => ?_
    have h := v.property
    rw [Submodule.mem_span_singleton] at h
    rcases h with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    ext
    exact hc

