import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {ι' : Type uι'} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} {M' : Type v'}

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [Module R M'] [Module R M₂]

variable {R M₂} {N : (ι ⊕ ι') → Type*}
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

theorem currySum_apply' {N : Type*} [AddCommMonoid N] [Module R N]
    (f : MultilinearMap R (fun _ : ι ⊕ ι' ↦ N) M₂)
    (u : ι → N) (v : ι' → N) :
    MultilinearMap.currySum f u v = f (Sum.elim u v) := rfl

