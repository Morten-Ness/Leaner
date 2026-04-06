FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_subtype_lt_map_subtype {G' : Subgroup G} {H K : Subgroup G'} :
    H.map G'.subtype < K.map G'.subtype ↔ H < K := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x hx
      have hx' : (x : G) ∈ H.map G'.subtype := ⟨x, hx, rfl⟩
      exact h.1 hx'
    · intro hKH
      apply h.2
      apply le_antisymm
      · exact h.1
      · intro x hx
        rcases hx with ⟨y, hy, hyx⟩
        have : y ∈ H := hKH hy
        rcases Subtype.ext_iff.mp hyx with hyx'
        simpa [hyx'] using this
  · intro h
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨y, h.1 hy, rfl⟩
    · intro hmap
      apply h.2
      intro x hx
      have hx' : (x : G) ∈ K.map G'.subtype := ⟨x, hx, rfl⟩
      have hx'' : (x : G) ∈ H.map G'.subtype := hmap hx'
      rcases hx'' with ⟨y, hy, hyx⟩
      rcases Subtype.ext_iff.mp hyx with hyx'
      simpa [hyx'] using hy
