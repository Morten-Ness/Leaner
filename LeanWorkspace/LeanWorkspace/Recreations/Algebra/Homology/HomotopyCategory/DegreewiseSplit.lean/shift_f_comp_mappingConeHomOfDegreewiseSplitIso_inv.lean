import Mathlib

variable {C : Type*} [Category.{v} C] [Preadditive C]

variable (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (eval C _ n)).Splitting)

variable [HasBinaryBiproducts C]

set_option backward.isDefEq.respectTransparency false in
theorem shift_f_comp_mappingConeHomOfDegreewiseSplitIso_inv :
    S.f⟦(1 : ℤ)⟧' ≫ (CochainComplex.mappingConeHomOfDegreewiseSplitIso S σ).inv = -mappingCone.inr _ := by
  ext n
  have h := (σ (n + 1)).f_r
  dsimp at h
  dsimp [CochainComplex.mappingConeHomOfDegreewiseSplitXIso]
  rw [id_comp, comp_sub, ← comp_f_assoc, S.zero, zero_f, zero_comp, zero_sub, reassoc_of% h]

