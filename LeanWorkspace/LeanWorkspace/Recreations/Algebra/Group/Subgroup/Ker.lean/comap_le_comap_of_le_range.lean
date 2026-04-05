import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem comap_le_comap_of_le_range {f : G →* N} {K L : Subgroup N} (hf : K ≤ f.range) :
    K.comap f ≤ L.comap f ↔ K ≤ L := ⟨(Subgroup.map_comap_eq_self hf).ge.trans ∘ map_le_iff_le_comap.mpr, comap_mono⟩

