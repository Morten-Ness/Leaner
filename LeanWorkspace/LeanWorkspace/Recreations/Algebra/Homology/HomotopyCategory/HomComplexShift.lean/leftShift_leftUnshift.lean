import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

theorem leftShift_leftUnshift {a n' : ℤ} (γ : CochainComplex.HomComplex.Cochain (K⟦a⟧) L n') (n : ℤ) (hn' : n + a = n') :
    (γ.leftUnshift n hn').leftShift a n' hn' = γ := by
  ext p q hpq
  rw [CochainComplex.HomComplex.Cochain.leftShift_v (γ.leftUnshift n hn') a n' hn' p q hpq (q - n) (by lia),
    γ.leftUnshift_v n hn' (q - n) q (by lia) p hpq, Linear.comp_units_smul, smul_smul,
    Iso.hom_inv_id_assoc, Int.units_mul_self, one_smul]

