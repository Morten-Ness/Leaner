import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem toSubmonoid_zpowers (g : G) :
    (Subgroup.zpowers g).toSubmonoid = Submonoid.powers g ⊔ Submonoid.powers g⁻¹ := by
  rw [zpowers_eq_closure, Subgroup.closure_toSubmonoid, Submonoid.closure_union,
    Submonoid.powers_eq_closure, Submonoid.powers_eq_closure, Set.inv_singleton]

