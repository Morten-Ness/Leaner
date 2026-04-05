import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {ι : Type*} {M : ι → Type*} [∀ i, MulOneClass (M i)]

theorem pi_empty (H : ∀ i, Submonoid (M i)) : Submonoid.pi ∅ H = ⊤ := ext fun x => by simp [Submonoid.mem_pi]

