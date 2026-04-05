import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem dNext_eq (f : ∀ i j, C.X i ⟶ D.X j) {i i' : ι} (w : c.Rel i i') :
    dNext i f = C.d i i' ≫ f i' i := by
  obtain rfl := c.next_eq' w
  rfl

