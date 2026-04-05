import Mathlib

variable {R L₁ L₂ L L₃ L₄ L₅ L₆ : Type*}
  [CommRing R] [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂] [LieAlgebra R L₂]
  [LieRing L] [LieAlgebra R L] [LieRing L₃] [LieAlgebra R L₃] [LieRing L₄] [LieAlgebra R L₄]
  [LieRing L₅] [LieAlgebra R L₅] [LieRing L₆] [LieAlgebra R L₆]

theorem prod_ext {f g : L₁ × L₂ →ₗ⁅R⁆ L} (hl : f.comp (LieHom.inl _ _ _) = g.comp (LieHom.inl _ _ _))
    (hr : f.comp (LieHom.inr _ _ _) = g.comp (LieHom.inr _ _ _)) : f = g := by
  refine (LieHom.prod_ext_iff R L₁ L₂).mpr ⟨hl,hr⟩

