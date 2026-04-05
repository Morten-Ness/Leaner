import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasDerivedCategory.{w} C]

set_option backward.isDefEq.respectTransparency false in
theorem singleFunctorsPostcompQIso_inv_hom (n : ℤ) :
    (DerivedCategory.singleFunctorsPostcompQIso C).inv.hom n = 𝟙 _ := by
  ext X
  simp [DerivedCategory.singleFunctorsPostcompQIso, HomotopyCategory.singleFunctorsPostcompQuotientIso]
  rfl

