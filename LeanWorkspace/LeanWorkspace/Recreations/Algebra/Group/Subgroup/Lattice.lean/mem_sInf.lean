import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem mem_sInf {S : Set (Subgroup G)} {x : G} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := Set.mem_iInter₂

