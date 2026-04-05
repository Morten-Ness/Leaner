import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {ι : Type*} {M : ι → Type*} [∀ i, MulOneClass (M i)]

theorem pi_bot : (Submonoid.pi Set.univ fun i => (⊥ : Submonoid (M i))) = ⊥ := ext fun x => by simp [Submonoid.mem_pi, funext_iff]

