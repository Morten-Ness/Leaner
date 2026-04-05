import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem prevD_eq_zero (f : ∀ i j, C.X i ⟶ D.X j) (i : ι) (hi : ¬ c.Rel (c.prev i) i) :
    prevD i f = 0 := by
  dsimp [prevD]
  rw [shape _ _ _ hi, comp_zero]

