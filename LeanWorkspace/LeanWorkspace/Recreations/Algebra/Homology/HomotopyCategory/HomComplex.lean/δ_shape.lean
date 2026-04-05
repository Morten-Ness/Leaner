import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem δ_shape (hnm : ¬ n + 1 = m) (z : CochainComplex.HomComplex.Cochain F G n) : CochainComplex.HomComplex.δ n m z = 0 := by
  ext p q hpq
  dsimp only [CochainComplex.HomComplex.δ]
  rw [CochainComplex.HomComplex.Cochain.mk_v, CochainComplex.HomComplex.Cochain.zero_v, F.shape, G.shape, comp_zero, zero_add, zero_comp, smul_zero]
  all_goals
    simp only [ComplexShape.up_Rel]
    exact fun _ => hnm (by lia)

