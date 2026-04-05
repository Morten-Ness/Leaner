import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem prevD_eq_toPrev_dTo (f : ∀ i j, C.X i ⟶ D.X j) (j : ι) :
    prevD j f = toPrev j f ≫ D.dTo j := rfl

