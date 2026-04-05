import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem exists_mem_zpowers {x : G} {p : G → Prop} : (∃ g ∈ Subgroup.zpowers x, p g) ↔ ∃ m : ℤ, p (x ^ m) := Set.exists_range_iff

