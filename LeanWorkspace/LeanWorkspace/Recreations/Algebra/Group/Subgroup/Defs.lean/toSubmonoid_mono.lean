import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

theorem toSubmonoid_mono : Monotone (toSubmonoid : Subgroup G → Submonoid G) := Subgroup.toSubmonoid_strictMono.monotone

