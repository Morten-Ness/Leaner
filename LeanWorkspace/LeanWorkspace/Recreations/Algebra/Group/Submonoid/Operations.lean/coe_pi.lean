import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {ι : Type*} {M : ι → Type*} [∀ i, MulOneClass (M i)]

theorem coe_pi (I : Set ι) (S : ∀ i, Submonoid (M i)) :
    (Submonoid.pi I S : Set (∀ i, M i)) = Set.pi I fun i => (S i : Set (M i)) := rfl

