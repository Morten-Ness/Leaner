import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem ofHoms_comp (φ : ∀ (p : ℤ), F.X p ⟶ G.X p) (ψ : ∀ (p : ℤ), G.X p ⟶ K.X p) :
    (CochainComplex.HomComplex.Cochain.ofHoms φ).comp (CochainComplex.HomComplex.Cochain.ofHoms ψ) (zero_add 0) = CochainComplex.HomComplex.Cochain.ofHoms (fun p => φ p ≫ ψ p) := by cat_disch

