import Mathlib

variable {ι R : Type*} {S : ι → Type*} [CommSemiring R] [∀ i, Semiring (S i)] [∀ i, Algebra R (S i)]
  {s : Set ι} {t t₁ t₂ : ∀ i, Subalgebra R (S i)} {x : ∀ i, S i}

theorem pi_top (s : Set ι) : Subalgebra.pi s (fun i ↦ (⊤ : Subalgebra R (S i))) = ⊤ := SetLike.coe_injective <| Set.pi_univ _

