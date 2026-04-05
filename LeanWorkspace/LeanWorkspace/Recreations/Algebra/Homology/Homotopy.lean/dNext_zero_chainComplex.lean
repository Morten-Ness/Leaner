import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

variable {P Q : ChainComplex V ℕ}

theorem dNext_zero_chainComplex (f : ∀ i j, P.X i ⟶ Q.X j) : dNext 0 f = 0 := by
  dsimp [dNext]
  rw [P.shape, zero_comp]
  rw [ChainComplex.next_nat_zero]; dsimp; decide

