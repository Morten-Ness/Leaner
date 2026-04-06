FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem Normal.of_map_subtype {K : Subgroup G} {L : Subgroup K}
    (n : (Subgroup.map K.subtype L).Normal) : L.Normal :=
by
  refine ⟨?_⟩
  intro a ha g
  have hmap : ((g * a * g⁻¹ : K) : G) ∈ Subgroup.map K.subtype L := by
    exact n.conj_mem (show ((a : K) : G) ∈ Subgroup.map K.subtype L from ⟨a, ha, rfl⟩) (g : G)
  rcases hmap with ⟨x, hx, hxeq⟩
  change (g * a * g⁻¹ : K) = x at hxeq
  rw [hxeq]
  exact hx
