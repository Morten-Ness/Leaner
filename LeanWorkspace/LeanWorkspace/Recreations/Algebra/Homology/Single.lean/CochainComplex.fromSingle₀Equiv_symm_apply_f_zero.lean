import Mathlib

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

theorem fromSingle₀Equiv_symm_apply_f_zero {C : CochainComplex V ℕ} {X : V}
    (f : X ⟶ C.X 0) (hf : f ≫ C.d 0 1 = 0) :
    ((CochainComplex.fromSingle₀Equiv C X).symm ⟨f, hf⟩).f 0 = f := by
  simp [CochainComplex.fromSingle₀Equiv]

