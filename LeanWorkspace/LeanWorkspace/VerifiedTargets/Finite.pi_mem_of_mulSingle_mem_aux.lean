import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {η : Type*} {f : η → Type*} [∀ i, Group (f i)]

theorem pi_mem_of_mulSingle_mem_aux [DecidableEq η] (I : Finset η) {H : Subgroup (∀ i, f i)}
    (x : ∀ i, f i) (h1 : ∀ i, i ∉ I → x i = 1) (h2 : ∀ i, i ∈ I → Pi.mulSingle i (x i) ∈ H) :
    x ∈ H := Submonoid.pi_mem_of_mulSingle_mem_aux I x h1 h2

