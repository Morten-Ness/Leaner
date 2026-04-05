import Mathlib

variable {R : Type*}

variable {G : Type*} [Group G] [StarMul G]

theorem mem_unitarySubgroup_iff {g : G} : g ∈ unitarySubgroup G ↔ g ∈ unitary G := Iff.rfl

nonrec theorem Unitary.inv_mem_iff {g : G} : g⁻¹ ∈ unitary G ↔ g ∈ unitary G :=
  inv_mem_iff (H := unitarySubgroup G)

