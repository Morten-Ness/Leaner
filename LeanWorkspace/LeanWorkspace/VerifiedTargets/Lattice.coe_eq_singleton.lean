import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem coe_eq_singleton {H : Subgroup G} : (∃ g : G, (H : Set G) = {g}) ↔ H = ⊥ := ⟨fun ⟨g, hg⟩ =>
    haveI : Subsingleton (H : Set G) := by
      rw [hg]
      infer_instance
    H.eq_bot_of_subsingleton,
    fun h => ⟨1, SetLike.ext'_iff.mp h⟩⟩

