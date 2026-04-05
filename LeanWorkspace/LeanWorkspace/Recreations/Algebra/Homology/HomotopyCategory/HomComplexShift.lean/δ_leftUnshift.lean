import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

set_option backward.isDefEq.respectTransparency false in
theorem δ_leftUnshift {a n' : ℤ} (γ : CochainComplex.HomComplex.Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n')
    (m m' : ℤ) (hm' : m + a = m') :
    δ n m (γ.leftUnshift n hn) = a.negOnePow • (δ n' m' γ).leftUnshift m hm' := by
  obtain ⟨γ', rfl⟩ := (CochainComplex.HomComplex.Cochain.leftShiftAddEquiv K L n a n' hn).surjective γ
  dsimp
  simp only [CochainComplex.HomComplex.Cochain.leftUnshift_leftShift, γ'.δ_leftShift a n' m' hn m hm', CochainComplex.HomComplex.Cochain.leftUnshift_units_smul,
    smul_smul, Int.units_mul_self, one_smul]

