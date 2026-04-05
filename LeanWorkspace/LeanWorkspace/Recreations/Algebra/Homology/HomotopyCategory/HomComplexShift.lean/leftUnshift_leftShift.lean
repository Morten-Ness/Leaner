import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

theorem leftUnshift_leftShift (a n' : ℤ) (hn' : n + a = n') :
    (γ.leftShift a n' hn').leftUnshift n hn' = γ := by
  ext p q hpq
  rw [CochainComplex.HomComplex.Cochain.leftUnshift_v (γ.leftShift a n' hn') n hn' p q hpq (q - n') (by lia),
    γ.leftShift_v a n' hn' (q - n') q (by lia) p hpq, Linear.comp_units_smul,
    Iso.inv_hom_id_assoc, smul_smul, Int.units_mul_self, one_smul]

