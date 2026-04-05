import Mathlib

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

theorem fromSingle₀Equiv_symm_apply_f_succ
    {C : ChainComplex V ℕ} {X : V} (f : X ⟶ C.X 0) (n : ℕ) :
    ((ChainComplex.fromSingle₀Equiv C X).symm f).f (n + 1) = 0 := rfl

