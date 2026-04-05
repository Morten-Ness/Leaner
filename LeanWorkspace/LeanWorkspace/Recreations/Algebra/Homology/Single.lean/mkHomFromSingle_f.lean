import Mathlib

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

variable {ι : Type*} [DecidableEq ι] (c : ComplexShape ι)

theorem mkHomFromSingle_f {K : HomologicalComplex V c} {j : ι} {A : V} (φ : A ⟶ K.X j)
    (hφ : ∀ (k : ι), c.Rel j k → φ ≫ K.d j k = 0) :
    (HomologicalComplex.mkHomFromSingle φ hφ).f j = (HomologicalComplex.singleObjXSelf c j A).hom ≫ φ := by
  dsimp [HomologicalComplex.mkHomFromSingle]
  rw [dif_pos rfl, comp_id]
  rfl

