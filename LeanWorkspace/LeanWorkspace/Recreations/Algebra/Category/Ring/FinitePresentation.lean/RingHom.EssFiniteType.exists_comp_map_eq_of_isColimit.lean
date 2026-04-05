import Mathlib

variable {J : Type uJ} [Category.{vJ} J] [IsFiltered J]

variable (R : CommRingCat.{u}) (F : J ⥤ CommRingCat.{u}) (α : (Functor.const _).obj R ⟶ F)

variable {S : CommRingCat.{u}} (f : R ⟶ S) (c : Cocone F) (hc : IsColimit c)

variable [PreservesColimit F (forget CommRingCat)]

set_option backward.isDefEq.respectTransparency false in
include hc in
theorem RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit (hf : f.hom.EssFiniteType)
    {i : J} (a : S ⟶ F.obj i) (ha : f ≫ a = α.app i)
    {j : J} (b : S ⟶ F.obj j) (hb : f ≫ b = α.app j)
    (hab : a ≫ c.ι.app i = b ≫ c.ι.app j) :
    ∃ (k : J) (hik : i ⟶ k) (hjk : j ⟶ k),
      a ≫ F.map hik = b ≫ F.map hjk := by
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  choose k f₁ f₂ h using fun x : S ↦
    (Types.FilteredColimit.isColimit_eq_iff _ hc').mp congr(($hab).hom x)
  let J' : MulticospanShape := ⟨Unit ⊕ Unit, hf.finset, fun _ ↦ .inl .unit, fun _ ↦ .inr .unit⟩
  let D : MulticospanIndex J' J :=
  { left := Sum.elim (fun _ ↦ i) (fun _ ↦ j)
    right x := k x.1
    fst x := f₁ x
    snd x := f₂ x }
  obtain ⟨c'⟩ := IsFiltered.cocone_nonempty D.multicospan
  refine ⟨c'.pt, c'.ι.app (.left (.inl .unit)), c'.ι.app (.left (.inr .unit)), ?_⟩
  ext1
  apply hf.ext
  · rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, reassoc_of% ha, reassoc_of% hb]
    simp [← α.naturality]
  · intro x hx
    rw [← c'.w (.fst (by exact ⟨x, hx⟩)), ← c'.w (.snd (by exact ⟨x, hx⟩))]
    have (x : _) : F.map (f₁ x) (a x) = F.map (f₂ x) (b x) := h x
    simp [D, this]

