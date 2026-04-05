import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

variable {n} {D : Type*} [Category* D] [Preadditive D] (z z' : Cochain K L n) (f : K ⟶ L)
  (Φ : C ⥤ D) [Φ.Additive]

set_option backward.isDefEq.respectTransparency false in
theorem map_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : CochainComplex.HomComplex.Cochain F G n₁) (z₂ : CochainComplex.HomComplex.Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
    (Φ : C ⥤ D) [Φ.Additive] :
    (CochainComplex.HomComplex.Cochain.comp z₁ z₂ h).map Φ = CochainComplex.HomComplex.Cochain.comp (z₁.map Φ) (z₂.map Φ) h := by
  ext p q hpq
  dsimp
  simp only [CochainComplex.HomComplex.Cochain.map_v, CochainComplex.HomComplex.Cochain.comp_v _ _ h p _ q rfl (by lia), Φ.map_comp]

