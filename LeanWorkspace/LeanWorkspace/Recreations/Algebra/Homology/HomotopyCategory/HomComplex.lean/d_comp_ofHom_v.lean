import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem d_comp_ofHom_v (φ : F ⟶ G) (p' p q : ℤ) (hpq : p + 0 = q) :
    F.d p' p ≫ (CochainComplex.HomComplex.Cochain.ofHom φ).v p q hpq = F.d p' q ≫ φ.f q := by
  simp only [CochainComplex.HomComplex.Cochain.ofHom, CochainComplex.HomComplex.Cochain.d_comp_ofHoms_v]

