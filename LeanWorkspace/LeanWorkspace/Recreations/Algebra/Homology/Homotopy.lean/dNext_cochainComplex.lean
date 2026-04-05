import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

variable {P Q : CochainComplex V ℕ}

theorem dNext_cochainComplex (f : ∀ i j, P.X i ⟶ Q.X j) (j : ℕ) :
    dNext j f = P.d _ _ ≫ f (j + 1) j := by
  dsimp [dNext]
  have : (ComplexShape.up ℕ).next j = j + 1 := CochainComplex.next ℕ j
  congr 2

-- This is not a simp lemma; the LHS already simplifies.

