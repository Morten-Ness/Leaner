import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Module R A] [Module S A]

variable [Algebra R S] {a : A} {f : S → R}

variable [IsScalarTower S A A] [SMulCommClass S A A]

variable [IsScalarTower R S A]

theorem subset_preimage (h : QuasispectrumRestricts a f) :
    quasispectrum S a ⊆ f ⁻¹' quasispectrum R a := QuasispectrumRestricts.image h ▸ (quasispectrum S a).subset_preimage_image f

protected lemma comp {R₁ R₂ R₃ A : Type*} [Semifield R₁] [Field R₂] [Field R₃]
    [NonUnitalRing A] [Module R₁ A] [Module R₂ A] [Module R₃ A] [Algebra R₁ R₂] [Algebra R₂ R₃]
    [Algebra R₁ R₃] [IsScalarTower R₁ R₂ R₃] [IsScalarTower R₂ R₃ A] [IsScalarTower R₃ A A]
    [SMulCommClass R₃ A A] {a : A} {f : R₃ → R₂} {g : R₂ → R₁} {e : R₃ → R₁} (hfge : g ∘ f = e)
    (hf : QuasispectrumRestricts a f) (hg : QuasispectrumRestricts a g) :
    QuasispectrumRestricts a e where
  left_inv := by
    convert hfge ▸ hf.left_inv.comp hg.left_inv
    congrm (⇑$(IsScalarTower.algebraMap_eq R₁ R₂ R₃))
  rightInvOn := by
    convert hfge ▸ hg.rightInvOn.comp hf.rightInvOn fun _ ↦ QuasispectrumRestricts.apply_mem hf
    congrm (⇑$(IsScalarTower.algebraMap_eq R₁ R₂ R₃))

