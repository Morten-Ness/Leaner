import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}

variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

variable [Semiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommGroup M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂] (f g : MultilinearMap R M₁ M₂)

theorem neg_apply (m : ∀ i, M₁ i) : (-f) m = -f m := rfl

