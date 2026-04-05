import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem _root_.Submonoid.powers_le_zpowers (g : G) :
    Submonoid.powers g ≤ (Subgroup.zpowers g).toSubmonoid := by
  rw [Subgroup.toSubmonoid_zpowers]
  exact le_sup_left

