import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem mk_eq_one {g : G} {h} : (⟨g, h⟩ : H) = 1 ↔ g = 1 := Submonoid.mk_eq_one ..

