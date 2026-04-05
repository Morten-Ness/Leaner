import Mathlib

variable {G H M N α : Type*}

theorem IsUnit.smul [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
    {m : M} (g : G) (h : IsUnit m) : IsUnit (g • m) := let ⟨u, hu⟩ := h
  hu ▸ ⟨g • u, Units.val_smul _ _⟩

