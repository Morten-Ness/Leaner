import Mathlib

variable {R ι₁ ι₂ ι₃ ι₄ : Type*}

variable [CommSemiring R]

variable {N₁ : Type*} [AddCommMonoid N₁] [Module R N₁]

variable {N₂ : Type*} [AddCommMonoid N₂] [Module R N₂]

variable {N : Type*} [AddCommMonoid N] [Module R N]

theorem domCoprod'_apply (a : MultilinearMap R (fun _ : ι₁ => N) N₁)
    (b : MultilinearMap R (fun _ : ι₂ => N) N₂) : MultilinearMap.domCoprod' (a ⊗ₜ[R] b) = MultilinearMap.domCoprod a b := rfl

