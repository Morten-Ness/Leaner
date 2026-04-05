import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

variable {P Q : ChainComplex V ℕ}

theorem prevD_chainComplex (f : ∀ i j, P.X i ⟶ Q.X j) (j : ℕ) :
    prevD j f = f j (j + 1) ≫ Q.d _ _ := by
  dsimp [prevD]
  have : (ComplexShape.down ℕ).prev j = j + 1 := ChainComplex.prev ℕ j
  congr 2

-- This is not a simp lemma; the LHS already simplifies.

