import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem coe_mk (x : G) (hx : x ∈ H) : ((⟨x, hx⟩ : H) : G) = x := rfl

