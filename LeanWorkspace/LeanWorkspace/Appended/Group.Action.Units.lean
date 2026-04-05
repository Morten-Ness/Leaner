import Mathlib

section

variable {G H M N α : Type*}

theorem IsUnit.smul [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
    {m : M} (g : G) (h : IsUnit m) : IsUnit (g • m) := let ⟨u, hu⟩ := h
  hu ▸ ⟨g • u, Units.val_smul _ _⟩

end

section

variable {G H M N α : Type*}

theorem smul_eq_mul {M} [CommMonoid M] (u₁ u₂ : Mˣ) :
    u₁ • u₂ = u₁ * u₂ := by
  fail_if_success rfl -- there is an instance diamond here
  ext
  rfl

end
