import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem extendMap_f {i : ι} {i' : ι'} (h : e.f i = i') :
    (HomologicalComplex.extendMap φ e).f i' =
      (HomologicalComplex.extendXIso K e h).hom ≫ φ.f i ≫ (HomologicalComplex.extendXIso L e h).inv := by
  dsimp [HomologicalComplex.extendMap]
  rw [HomologicalComplex.extend.mapX_some HomologicalComplex.extend φ (e.r_eq_some h)]
  rfl

