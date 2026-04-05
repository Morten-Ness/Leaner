import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {H : Subgroup G}

theorem mem_comm_iff (nH : H.Normal) {a b : G} : a * b ∈ H ↔ b * a ∈ H := ⟨Subgroup.Normal.mem_comm nH, Subgroup.Normal.mem_comm nH⟩

