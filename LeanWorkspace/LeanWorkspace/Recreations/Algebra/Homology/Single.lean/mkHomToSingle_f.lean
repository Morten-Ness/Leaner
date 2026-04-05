import Mathlib

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

variable {ι : Type*} [DecidableEq ι] (c : ComplexShape ι)

theorem mkHomToSingle_f {K : HomologicalComplex V c} {j : ι} {A : V} (φ : K.X j ⟶ A)
    (hφ : ∀ (i : ι), c.Rel i j → K.d i j ≫ φ = 0) :
    (HomologicalComplex.mkHomToSingle φ hφ).f j = φ ≫ (HomologicalComplex.singleObjXSelf c j A).inv := by
  dsimp [HomologicalComplex.mkHomToSingle]
  rw [dif_pos rfl, id_comp]
  rfl

