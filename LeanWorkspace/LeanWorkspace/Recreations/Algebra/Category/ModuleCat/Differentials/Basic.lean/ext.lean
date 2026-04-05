import Mathlib

variable {A B A' B' : CommRingCat.{u}} {f : A ⟶ B} {f' : A' ⟶ B'}
  {g : A ⟶ A'} {g' : B ⟶ B'} (fac : g ≫ f' = f ≫ g')

set_option backward.isDefEq.respectTransparency false in
theorem ext {M : ModuleCat B} {α β : CommRingCat.KaehlerDifferential f ⟶ M}
    (h : ∀ (b : B), α (ModuleCat.Derivation.d b) = β (ModuleCat.Derivation.d b)) : α = β := by
  rw [← sub_eq_zero]
  have : ⊤ ≤ LinearMap.ker (α - β).hom := by
    rw [← CommRingCat.KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ModuleCat.hom_sub, LinearMap.sub_apply, sub_eq_zero]
    apply h
  rw [top_le_iff, LinearMap.ker_eq_top] at this
  ext : 1
  exact this

