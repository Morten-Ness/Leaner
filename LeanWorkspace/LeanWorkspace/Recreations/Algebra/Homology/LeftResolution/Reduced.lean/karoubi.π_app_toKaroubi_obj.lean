import Mathlib

variable {A C : Type*} [Category* C] [Category* A] {ι : C ⥤ A}
  (Λ : LeftResolution ι)

variable [Preadditive C] [Preadditive A] [ι.Additive]

set_option backward.isDefEq.respectTransparency false in
theorem karoubi.π_app_toKaroubi_obj (X : A) :
    (CategoryTheory.Abelian.LeftResolution.karoubi.π Λ).app ((toKaroubi _).obj X) = (CategoryTheory.Abelian.LeftResolution.karoubi.π' Λ).app X := by
  simp [π, whiskeringLeftObjToKaroubiFullyFaithful]

