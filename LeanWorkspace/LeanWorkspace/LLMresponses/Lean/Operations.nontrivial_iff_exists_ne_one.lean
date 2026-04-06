FAIL
import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem nontrivial_iff_exists_ne_one (S : Submonoid M) : Nontrivial S ↔ ∃ x ∈ S, x ≠ (1 : M) := by
  constructor
  · intro h
    by_cases hS : ∀ x : S, x = 1
    · exfalso
      have hsub : Subsingleton S := ⟨fun x y => by rw [hS x, hS y]⟩
      exact h.ne_iff.mp (Subsingleton.elim _ _)
    · have hS' : ∃ x : S, x ≠ 1 := by
        by_contra h'
        apply hS
        intro x
        by_contra hx
        exact h' ⟨x, hx⟩
      rcases hS' with ⟨x, hx⟩
      refine ⟨x, x.2, ?_⟩
      simpa using hx
  · rintro ⟨x, hx, hxne⟩
    refine ⟨⟨⟨x, hx⟩, 1, ?_⟩⟩
    intro h
    apply hxne
    simpa using congrArg Subtype.val h
