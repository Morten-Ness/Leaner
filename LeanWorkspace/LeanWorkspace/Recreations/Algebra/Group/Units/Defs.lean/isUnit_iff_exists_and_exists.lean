import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

theorem isUnit_iff_exists_and_exists [Monoid M] {a : M} :
    IsUnit a ↔ (∃ b, a * b = 1) ∧ (∃ c, c * a = 1) := isUnit_iff_exists.trans
    ⟨fun ⟨b, hba, hab⟩ => ⟨⟨b, hba⟩, ⟨b, hab⟩⟩,
      fun ⟨⟨b, hb⟩, ⟨_, hc⟩⟩ => ⟨b, hb, left_inv_eq_right_inv hc hb ▸ hc⟩⟩

