import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {ι : Type*} {M : ι → Type*} [∀ i, MulOneClass (M i)]

theorem le_pi_iff {I : Set ι} {S : ∀ i, Submonoid (M i)} {J : Submonoid (∀ i, M i)} :
    J ≤ Submonoid.pi I S ↔ ∀ i ∈ I, J ≤ Submonoid.comap (Pi.evalMonoidHom M i) (S i) := Set.subset_pi_iff

