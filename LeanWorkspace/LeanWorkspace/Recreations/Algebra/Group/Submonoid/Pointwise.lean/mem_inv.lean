import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable {s t u : Set M}

variable [Group G]

theorem mem_inv {g : G} {S : Submonoid G} : g ∈ S⁻¹ ↔ g⁻¹ ∈ S := Iff.rfl

