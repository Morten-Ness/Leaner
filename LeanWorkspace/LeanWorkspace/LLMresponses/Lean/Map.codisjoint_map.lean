FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem codisjoint_map {f : G →* N} (hf : Function.Surjective f)
    {H K : Subgroup G} (h : Codisjoint H K) : Codisjoint (H.map f) (K.map f) := by
  rw [show H ⊔ K = ⊤ from codisjoint_iff.mp h]
  ext n
  constructor
  · intro _
    trivial
  · intro _
    rcases hf n with ⟨g, rfl⟩
    exact Subgroup.mem_map.2 ⟨g, by simp, rfl⟩
