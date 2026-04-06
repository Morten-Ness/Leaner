FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_lt_map_iff_of_injective {f : G →* N} (hf : Function.Injective f) {H K : Subgroup G} :
    H.map f < K.map f ↔ H < K := by
  constructor
  · rintro ⟨hmap, hne⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      have hxmap : f x ∈ H.map f := ⟨x, hx, rfl⟩
      have hkmap : f x ∈ K.map f := hmap hxmap
      rcases hkmap with ⟨y, hy, hfy⟩
      have : y = x := hf (by simpa using hfy)
      simpa [this] using hy
    · intro hKH
      apply hne
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact ⟨x, hKH hx, rfl⟩
  · rintro ⟨hHK, hne⟩
    refine ⟨Subgroup.map_mono hHK, ?_⟩
    intro hEq
    apply hne
    intro x hx
    have hxmap : f x ∈ H.map f := ⟨x, hx, rfl⟩
    have hkmap : f x ∈ K.map f := by simpa [hEq] using hxmap
    rcases hkmap with ⟨y, hy, hfy⟩
    have : y = x := hf (by simpa using hfy)
    simpa [this] using hy
