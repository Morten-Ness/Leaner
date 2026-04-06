import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem exists_ne_one_of_nontrivial (H : Subgroup G) [Nontrivial H] :
    ∃ x ∈ H, x ≠ 1 := by
  rcases exists_pair_ne H with ⟨a, b, hab⟩
  by_cases ha : (a : G) ≠ 1
  · exact ⟨a, a.property, ha⟩
  · refine ⟨b, b.property, ?_⟩
    intro hb
    apply hab
    have ha' : (a : G) = 1 := by simpa using not_not.mp ha
    have hb' : (b : G) = 1 := hb
    apply Subtype.ext
    simp [ha', hb']
