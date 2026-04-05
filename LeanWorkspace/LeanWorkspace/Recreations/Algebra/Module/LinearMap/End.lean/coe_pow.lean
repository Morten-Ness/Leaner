import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]

theorem coe_pow (f : Module.End R M) (n : ℕ) : ⇑(f ^ n) = f^[n] := hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _

