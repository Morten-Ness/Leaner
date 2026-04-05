import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {η : Type*} {f : η → Type*} [∀ i, Group (f i)]

theorem pi_mem_of_mulSingle_mem [Finite η] [DecidableEq η] {H : Subgroup (∀ i, f i)} (x : ∀ i, f i)
    (h : ∀ i, Pi.mulSingle i (x i) ∈ H) : x ∈ H := Submonoid.pi_mem_of_mulSingle_mem x h

