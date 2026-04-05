import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem dNext_eq_zero (f : ∀ i j, C.X i ⟶ D.X j) (i : ι) (hi : ¬ c.Rel i (c.next i)) :
    dNext i f = 0 := by
  dsimp [dNext]
  rw [shape _ _ _ hi, zero_comp]

-- This is not a simp lemma; the LHS already simplifies.

