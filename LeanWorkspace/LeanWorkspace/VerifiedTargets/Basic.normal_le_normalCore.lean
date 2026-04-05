import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normal_le_normalCore {H : Subgroup G} {N : Subgroup G} [hN : N.Normal] :
    N ≤ H.normalCore ↔ N ≤ H := ⟨ge_trans H.normalCore_le, fun h_le n hn g => h_le (hN.conj_mem n hn g)⟩

