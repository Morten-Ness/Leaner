import Mathlib

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

theorem toSingle₀Equiv_symm_apply_f_succ
    {C : CochainComplex V ℕ} {X : V} (f : C.X 0 ⟶ X) (n : ℕ) :
    ((CochainComplex.toSingle₀Equiv C X).symm f).f (n + 1) = 0 := by
  rfl

