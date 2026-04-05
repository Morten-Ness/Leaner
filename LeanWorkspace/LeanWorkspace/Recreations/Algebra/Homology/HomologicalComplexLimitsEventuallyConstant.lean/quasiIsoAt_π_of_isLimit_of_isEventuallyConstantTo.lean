import Mathlib

variable {C J ι : Type*} [Category C] [Category J]
   {c : ComplexShape ι} [IsCofiltered J]

variable [HasZeroMorphisms C] (F : J ⥤ HomologicalComplex C c)
  [∀ (j : ι), HasLimit (F ⋙ eval C c j)]
  {cF : Cone F} (hcF : IsLimit cF)

theorem quasiIsoAt_π_of_isLimit_of_isEventuallyConstantTo
    [CategoryWithHomology C] (q₀ q₁ q₂ : ι)
    (h₀ : c.prev q₁ = q₀) (h₂ : c.next q₁ = q₂) (j : J)
    (hq₀ : (F ⋙ eval C c q₀).IsEventuallyConstantTo j)
    (hq₁ : (F ⋙ eval C c q₁).IsEventuallyConstantTo j)
    (hq₂ : (F ⋙ eval C c q₂).IsEventuallyConstantTo j) :
    QuasiIsoAt (cF.π.app j) q₁ := by
  rw [quasiIsoAt_iff' _ q₀ q₁ q₂ h₀ h₂]
  let φ := (shortComplexFunctor' C c q₀ q₁ q₂).map (cF.π.app j)
  have : IsIso φ.τ₁ := HomologicalComplex.isIso_π_f_of_isLimit_of_isEventuallyConstantTo F hcF _ _ hq₀
  have : IsIso φ.τ₂ := HomologicalComplex.isIso_π_f_of_isLimit_of_isEventuallyConstantTo F hcF _ _ hq₁
  have : IsIso φ.τ₃ := HomologicalComplex.isIso_π_f_of_isLimit_of_isEventuallyConstantTo F hcF _ _ hq₂
  apply ShortComplex.quasiIso_of_epi_of_isIso_of_mono

