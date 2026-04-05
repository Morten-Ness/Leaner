import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem δ_ofHom_comp {n : ℤ} (f : F ⟶ G) (z : CochainComplex.HomComplex.Cochain G K n) (m : ℤ) :
    CochainComplex.HomComplex.δ n m ((CochainComplex.HomComplex.Cochain.ofHom f).comp z (zero_add n)) =
      (CochainComplex.HomComplex.Cochain.ofHom f).comp (CochainComplex.HomComplex.δ n m z) (zero_add m) := by
  rw [← CochainComplex.HomComplex.Cocycle.ofHom_coe, CochainComplex.HomComplex.δ_zero_cocycle_comp]

