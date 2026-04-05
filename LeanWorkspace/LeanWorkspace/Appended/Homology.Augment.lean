import Mathlib

section

variable {V : Type u} [Category.{v} V]

variable [HasZeroMorphisms V]

theorem chainComplex_d_succ_succ_zero (C : ChainComplex V ℕ) (i : ℕ) : C.d (i + 2) 0 = 0 := by
  rw [C.shape]
  exact i.succ_succ_ne_one.symm

end

section

variable {V : Type u} [Category.{v} V]

variable [HasZeroMorphisms V]

theorem cochainComplex_d_succ_succ_zero (C : CochainComplex V ℕ) (i : ℕ) : C.d 0 (i + 2) = 0 := by
  rw [C.shape]
  simp only [ComplexShape.up_Rel, zero_add]
  exact (Nat.one_lt_succ_succ _).ne

end
