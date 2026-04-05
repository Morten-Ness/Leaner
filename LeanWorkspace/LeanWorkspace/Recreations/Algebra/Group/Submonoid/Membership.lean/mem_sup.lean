import Mathlib

variable {M A B : Type*}

variable {N : Type*} [CommMonoid N]

theorem mem_sup {s t : Submonoid N} {x : N} : x ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := by
  simp only [Submonoid.sup_eq_range, mem_mrange, coprod_apply, coe_subtype, Prod.exists,
    Subtype.exists, exists_prop]

