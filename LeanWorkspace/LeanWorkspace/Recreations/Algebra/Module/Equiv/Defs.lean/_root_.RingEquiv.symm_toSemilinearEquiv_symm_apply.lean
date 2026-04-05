import Mathlib

variable {R R₁ R₂ R₃ R₄ S M M₁ M₂ M₃ M₄ N₁ N₂ : Type*}

variable [Semiring R] [Semiring S]

theorem _root_.RingEquiv.symm_toSemilinearEquiv_symm_apply (f : R ≃+* S) (x : R) :
  f.symm.toSemilinearEquiv.symm (σ' := RingHomClass.toRingHom f) x = f x := rfl

