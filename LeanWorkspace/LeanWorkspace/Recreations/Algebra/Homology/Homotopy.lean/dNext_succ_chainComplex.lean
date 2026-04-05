import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

variable {P Q : ChainComplex V ℕ}

theorem dNext_succ_chainComplex (f : ∀ i j, P.X i ⟶ Q.X j) (i : ℕ) :
    dNext (i + 1) f = P.d _ _ ≫ f i (i + 1) := by
  dsimp [dNext]
  have : (ComplexShape.down ℕ).next (i + 1) = i := ChainComplex.next_nat_succ _
  congr 2

-- This is not a simp lemma; the LHS already simplifies.

