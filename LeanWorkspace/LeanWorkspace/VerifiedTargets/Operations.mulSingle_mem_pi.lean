import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {ι : Type*} {M : ι → Type*} [∀ i, MulOneClass (M i)]

theorem mulSingle_mem_pi [DecidableEq ι] {I : Set ι} {S : ∀ i, Submonoid (M i)} (i : ι) (x : M i) :
    Pi.mulSingle i x ∈ Submonoid.pi I S ↔ i ∈ I → x ∈ S i := Set.update_mem_pi_iff_of_mem (one_mem (Submonoid.pi I _))

