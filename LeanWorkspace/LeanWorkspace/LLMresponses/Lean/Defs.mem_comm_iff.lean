FAIL
import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {H : Subgroup G}

theorem mem_comm_iff (nH : H.Normal) {a b : G} : a * b ∈ H ↔ b * a ∈ H := by
  constructor
  · intro hab
    simpa [Subgroup.Normal, SetLike.mem] using nH (a * b) a hab
  · intro hba
    simpa [Subgroup.Normal, SetLike.mem] using nH (b * a) b hba
