import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
theorem isIso_descOpcycles_iff (K : ChainComplex C ℕ) {X : C} (φ : K.X 0 ⟶ X)
    [K.HasHomology 0] (hφ : K.d 1 0 ≫ φ = 0) :
    IsIso (K.descOpcycles φ 1 (by simp) hφ) ↔
      (ShortComplex.mk _ _ hφ).Exact ∧ Epi φ := by
  suffices ∀ (i : ℕ) (hx : (ComplexShape.down ℕ).prev 0 = i)
    (hφ : K.d i 0 ≫ φ = 0), IsIso (K.descOpcycles φ i hx hφ) ↔
      (ShortComplex.mk _ _ hφ).Exact ∧ Epi φ from this 1 (by simp) hφ
  rintro _ rfl hφ
  let α : K.sc 0 ⟶ ShortComplex.mk (0 : X ⟶ X) (0 : X ⟶ X) (by simp) :=
    { τ₁ := 0
      τ₂ := φ
      τ₃ := 0 }
  exact (ShortComplex.quasiIso_iff_isIso_descOpcycles α (by simp) rfl rfl).symm.trans
    (ShortComplex.quasiIso_iff_of_zeros' α (by simp) rfl rfl)

