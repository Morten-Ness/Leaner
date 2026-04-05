import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

variable {P Q : CochainComplex V ℕ}

theorem prevD_succ_cochainComplex (f : ∀ i j, P.X i ⟶ Q.X j) (i : ℕ) :
    prevD (i + 1) f = f (i + 1) _ ≫ Q.d i (i + 1) := by
  dsimp [prevD]
  have : (ComplexShape.up ℕ).prev (i + 1) = i := CochainComplex.prev_nat_succ i
  congr 2

-- This is not a simp lemma; the LHS already simplifies.

