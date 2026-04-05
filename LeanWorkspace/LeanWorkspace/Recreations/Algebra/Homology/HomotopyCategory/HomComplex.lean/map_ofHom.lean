import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

variable {n} {D : Type*} [Category* D] [Preadditive D] (z z' : Cochain K L n) (f : K ⟶ L)
  (Φ : C ⥤ D) [Φ.Additive]

theorem map_ofHom :
    (CochainComplex.HomComplex.Cochain.ofHom f).map Φ = CochainComplex.HomComplex.Cochain.ofHom ((Φ.mapHomologicalComplex _).map f) := by cat_disch

