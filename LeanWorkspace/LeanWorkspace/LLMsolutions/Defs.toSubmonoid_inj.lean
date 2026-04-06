import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

theorem toSubmonoid_inj {p q : Subgroup G} : p.toSubmonoid = q.toSubmonoid ↔ p = q := by
  constructor
  · intro h
    cases p
    cases q
    cases h
    rfl
  · intro h
    cases h
    rfl
