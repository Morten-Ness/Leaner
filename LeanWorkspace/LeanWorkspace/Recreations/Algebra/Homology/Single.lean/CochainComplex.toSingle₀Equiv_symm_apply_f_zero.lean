import Mathlib

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

theorem toSingle₀Equiv_symm_apply_f_zero
    {C : CochainComplex V ℕ} {X : V} (f : C.X 0 ⟶ X) :
    ((CochainComplex.toSingle₀Equiv C X).symm f).f 0 = f := by
  simp [CochainComplex.toSingle₀Equiv]

