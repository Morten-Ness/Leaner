import Mathlib

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]

variable (H : Subgroup G) [Nontrivial H] [hH : IsCyclic H]

theorem exists_generator_lt_one : ∃ (a : G), a < 1 ∧ LinearOrderedCommGroup.Subgroup.zpowers a = H := by
  obtain ⟨a, ha⟩ := H.isCyclic_iff_exists_zpowers_eq_top.mp hH
  obtain ha1 | rfl | ha1 := lt_trichotomy a 1
  · exact ⟨a, ha1, ha⟩
  · rw [LinearOrderedCommGroup.Subgroup.zpowers_one_eq_bot] at ha
    exact absurd ha.symm <| (H.nontrivial_iff_ne_bot).mp inferInstance
  · use a⁻¹, Left.inv_lt_one_iff.mpr ha1
    rw [LinearOrderedCommGroup.Subgroup.zpowers_inv, ha]

