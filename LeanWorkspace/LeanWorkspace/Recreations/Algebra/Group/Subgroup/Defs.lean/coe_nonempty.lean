import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

theorem coe_nonempty (s : Subgroup G) : (s : Set G).Nonempty := ⟨1, one_mem _⟩

