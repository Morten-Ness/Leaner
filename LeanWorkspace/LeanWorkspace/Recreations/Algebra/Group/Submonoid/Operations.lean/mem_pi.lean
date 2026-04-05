import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {ι : Type*} {M : ι → Type*} [∀ i, MulOneClass (M i)]

theorem mem_pi (I : Set ι) {S : ∀ i, Submonoid (M i)} {p : ∀ i, M i} :
    p ∈ Submonoid.pi I S ↔ ∀ i, i ∈ I → p i ∈ S i := Iff.rfl

