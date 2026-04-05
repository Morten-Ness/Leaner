import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem dNext_eq_dFrom_fromNext (f : ∀ i j, C.X i ⟶ D.X j) (i : ι) :
    dNext i f = C.dFrom i ≫ fromNext i f := rfl

