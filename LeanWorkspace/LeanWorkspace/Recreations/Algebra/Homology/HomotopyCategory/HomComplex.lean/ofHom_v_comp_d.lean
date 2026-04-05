import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem ofHom_v_comp_d (φ : F ⟶ G) (p q q' : ℤ) (hpq : p + 0 = q) :
    (CochainComplex.HomComplex.Cochain.ofHom φ).v p q hpq ≫ G.d q q' = φ.f p ≫ G.d p q' := by
  simp only [CochainComplex.HomComplex.Cochain.ofHom, CochainComplex.HomComplex.Cochain.ofHoms_v_comp_d]

