import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem ofHoms_v (ψ : ∀ (p : ℤ), F.X p ⟶ G.X p) (p : ℤ) :
    (CochainComplex.HomComplex.Cochain.ofHoms ψ).v p p (add_zero p) = ψ p := by
  simp only [CochainComplex.HomComplex.Cochain.ofHoms, CochainComplex.HomComplex.Cochain.mk_v, eqToHom_refl, comp_id]

