import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {η : Type*} {f : η → Type*} [∀ i, Group (f i)]

theorem pi_le_iff [DecidableEq η] [Finite η] {H : ∀ i, Subgroup (f i)} {J : Subgroup (∀ i, f i)} :
    pi Set.univ H ≤ J ↔ ∀ i : η, map (MonoidHom.mulSingle f i) (H i) ≤ J := Submonoid.pi_le_iff

