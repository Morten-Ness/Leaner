import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

theorem toSubmonoid_le {p q : Subgroup G} : p.toSubmonoid ≤ q.toSubmonoid ↔ p ≤ q := Iff.rfl

