import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem range_le_ker_iff (f : G →* G') (g : G' →* M) : f.range ≤ g.ker ↔ g.comp f = 1 := ⟨fun h => ext fun x => h ⟨x, rfl⟩, by rintro h _ ⟨y, rfl⟩; exact DFunLike.congr_fun h y⟩

