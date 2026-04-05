import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

theorem toSubmonoid_strictMono : StrictMono (toSubmonoid : Subgroup G → Submonoid G) := fun _ _ =>
  id

