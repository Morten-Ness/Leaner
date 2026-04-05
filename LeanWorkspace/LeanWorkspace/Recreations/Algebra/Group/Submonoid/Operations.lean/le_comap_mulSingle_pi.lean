import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {ι : Type*} {M : ι → Type*} [∀ i, MulOneClass (M i)]

theorem le_comap_mulSingle_pi [DecidableEq ι] (S : ∀ i, Submonoid (M i)) {I i} :
    S i ≤ Submonoid.comap (MonoidHom.mulSingle M i) (Submonoid.pi I S) := fun x hx => by simp [hx]

