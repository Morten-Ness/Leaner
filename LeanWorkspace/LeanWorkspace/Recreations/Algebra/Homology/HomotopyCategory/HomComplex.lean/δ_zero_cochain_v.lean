import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem δ_zero_cochain_v (z : CochainComplex.HomComplex.Cochain F G 0) (p q : ℤ) (hpq : p + 1 = q) :
    (CochainComplex.HomComplex.δ 0 1 z).v p q hpq = z.v p p (add_zero p) ≫ G.d p q - F.d p q ≫ z.v q q (add_zero q) := by
  simp only [CochainComplex.HomComplex.δ_v 0 1 (zero_add 1) z p q hpq p q (by lia) hpq, Int.negOnePow_one, Units.neg_smul,
    one_smul, sub_eq_add_neg]

