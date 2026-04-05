import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {ι' : Type uι'} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} {M' : Type v'}

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [Module R M'] [Module R M₂]

variable {R M₂} {N : (ι ⊕ ι') → Type*}
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

theorem uncurrySum_add
    (g₁ g₂ : MultilinearMap R (fun i : ι ↦ N (.inl i))
      (MultilinearMap R (fun i : ι' ↦ N (.inr i)) M₂)) :
    MultilinearMap.uncurrySum (g₁ + g₂) = MultilinearMap.uncurrySum g₁ + MultilinearMap.uncurrySum g₂ := rfl

