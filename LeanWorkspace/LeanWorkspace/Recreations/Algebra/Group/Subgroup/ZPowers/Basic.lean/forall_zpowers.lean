import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem forall_zpowers {x : G} {p : Subgroup.zpowers x → Prop} : (∀ g, p g) ↔ ∀ m : ℤ, p ⟨x ^ m, m, rfl⟩ := Set.forall_subtype_range_iff

-- increasing simp priority. Better lemma than `Subtype.exists`

