import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem prevD_eq (f : ∀ i j, C.X i ⟶ D.X j) {j j' : ι} (w : c.Rel j' j) :
    prevD j f = f j j' ≫ D.d j' j := by
  obtain rfl := c.prev_eq' w
  rfl

-- This is not a simp lemma; the LHS already simplifies.

