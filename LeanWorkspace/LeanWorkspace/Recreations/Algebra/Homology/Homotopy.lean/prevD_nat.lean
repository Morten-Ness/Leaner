import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem prevD_nat (C D : CochainComplex V ℕ) (i : ℕ) (f : ∀ i j, C.X i ⟶ D.X j) :
    prevD i f = f i (i - 1) ≫ D.d (i - 1) i := by
  dsimp [prevD]
  cases i
  · simp
  · congr <;> simp

