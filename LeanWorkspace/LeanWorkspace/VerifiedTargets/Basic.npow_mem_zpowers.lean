import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem npow_mem_zpowers (g : G) (k : ℕ) : g ^ k ∈ Subgroup.zpowers g := zpow_natCast g k ▸ Subgroup.zpow_mem_zpowers g k

-- increasing simp priority. Better lemma than `Subtype.exists`

