import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

variable {P Q : CochainComplex V ℕ}

theorem prevD_zero_cochainComplex (f : ∀ i j, P.X i ⟶ Q.X j) : prevD 0 f = 0 := by
  dsimp [prevD]
  rw [Q.shape, comp_zero]
  rw [CochainComplex.prev_nat_zero]; dsimp; decide

