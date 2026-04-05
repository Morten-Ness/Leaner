import Mathlib

variable {R ι₁ ι₂ ι₃ ι₄ : Type*}

variable [CommSemiring R]

variable {N₁ : Type*} [AddCommMonoid N₁] [Module R N₁]

variable {N₂ : Type*} [AddCommMonoid N₂] [Module R N₂]

variable {N : ι₁ ⊕ ι₂ → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

theorem domCoprodDep'_apply (a : MultilinearMap R (fun i₁ ↦ N (.inl i₁)) N₁)
    (b : MultilinearMap R (fun i₂ ↦ N (.inr i₂)) N₂) :
    MultilinearMap.domCoprodDep' (a ⊗ₜ b) = MultilinearMap.domCoprodDep a b := by
  rfl

