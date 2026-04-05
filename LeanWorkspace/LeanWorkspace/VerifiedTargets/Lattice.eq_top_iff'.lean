import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem eq_top_iff' : H = ⊤ ↔ ∀ x : G, x ∈ H := eq_top_iff.trans ⟨fun h m => h <| Subgroup.mem_top m, fun h m _ => h m⟩

