import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem exists_zpowers {x : G} {p : Subgroup.zpowers x → Prop} : (∃ g, p g) ↔ ∃ m : ℤ, p ⟨x ^ m, m, rfl⟩ := Set.exists_subtype_range_iff

