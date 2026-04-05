import Mathlib

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

theorem isScalarTower_iff_smulCommClass_of_commMonoid (R₁ R : Type*)
    [Monoid R₁] [CommMonoid R] [MulAction R₁ R] :
    SMulCommClass R₁ R R ↔ IsScalarTower R₁ R R := ⟨fun _ ↦ IsScalarTower.of_commMonoid R₁ R, fun _ ↦ SMulCommClass.of_commMonoid R₁ R R⟩

