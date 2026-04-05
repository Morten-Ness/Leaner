import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

variable {n} {D : Type*} [Category* D] [Preadditive D] (z z' : Cochain K L n) (f : K ⟶ L)
  (Φ : C ⥤ D) [Φ.Additive]

set_option backward.isDefEq.respectTransparency false in
theorem δ_map : CochainComplex.HomComplex.δ n m (z.map Φ) = (CochainComplex.HomComplex.δ n m z).map Φ := by
  by_cases hnm : n + 1 = m
  · CochainComplex.HomComplex.Cochain.ext p q hpq
    dsimp
    simp only [CochainComplex.HomComplex.δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl,
      Functor.map_add, Functor.map_comp, Functor.map_units_smul,
      CochainComplex.HomComplex.Cochain.map_v, Functor.mapHomologicalComplex_obj_d]
  · simp only [CochainComplex.HomComplex.δ_shape _ _ hnm, CochainComplex.HomComplex.Cochain.map_zero]

