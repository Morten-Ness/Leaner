import Mathlib

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

theorem toSingle₀Equiv_symm_apply_f_zero {C : ChainComplex V ℕ} {X : V}
    (f : C.X 0 ⟶ X) (hf : C.d 1 0 ≫ f = 0) :
    ((ChainComplex.toSingle₀Equiv C X).symm ⟨f, hf⟩).f 0 = f := by
  simp [ChainComplex.toSingle₀Equiv]

