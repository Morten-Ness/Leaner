import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {H : Subgroup G}

theorem mem_comm (nH : H.Normal) {a b : G} (h : a * b ∈ H) : b * a ∈ H := by
  have : a⁻¹ * (a * b) * a⁻¹⁻¹ ∈ H := nH.conj_mem (a * b) h a⁻¹
  simpa

