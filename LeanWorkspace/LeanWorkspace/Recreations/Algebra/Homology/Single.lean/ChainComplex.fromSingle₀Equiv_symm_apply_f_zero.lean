import Mathlib

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

theorem fromSingle₀Equiv_symm_apply_f_zero
    {C : ChainComplex V ℕ} {X : V} (f : X ⟶ C.X 0) :
    dsimp% ((ChainComplex.fromSingle₀Equiv C X).symm f).f 0 = f := by
  simp [ChainComplex.fromSingle₀Equiv]

