import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  {abv : β → α} [IsAbsoluteValue abv] {f g : ℕ → β}

theorem bounded (hf : IsCauSeq abv f) : ∃ r, ∀ i, abv (f i) < r := by
  obtain ⟨i, h⟩ := hf _ zero_lt_one
  set R : ℕ → α := @Nat.rec (fun _ => α) (abv (f 0)) fun i c => max c (abv (f i.succ)) with hR
  have : ∀ i, ∀ j ≤ i, abv (f j) ≤ R i := by
    refine Nat.rec (by simp [hR]) ?_
    rintro i hi j (rfl | hj)
    · simp [R]
    · exact (hi j hj).trans (le_max_left _ _)
  refine ⟨R i + 1, fun j ↦ ?_⟩
  obtain hji | hij := le_total j i
  · exact (this i _ hji).trans_lt (lt_add_one _)
  · simpa using (abv_add abv _ _).trans_lt <| add_lt_add_of_le_of_lt (this i _ le_rfl) (h _ hij)

