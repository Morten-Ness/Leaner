import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem mem_torsionBySet_iff (x : M) : x ∈ Submodule.torsionBySet R M s ↔ ∀ a : s, (a : R) • x = 0 := by
  refine ⟨fun h ⟨a, ha⟩ => mem_sInf.mp h _ (Set.mem_image_of_mem _ ha), fun h => mem_sInf.mpr ?_⟩
  rintro _ ⟨a, ha, rfl⟩; exact h ⟨a, ha⟩

