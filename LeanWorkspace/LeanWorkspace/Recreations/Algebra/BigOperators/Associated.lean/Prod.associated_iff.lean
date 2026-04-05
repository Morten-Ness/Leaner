import Mathlib

variable {ι M M₀ : Type*}

theorem Prod.associated_iff {M N : Type*} [Monoid M] [Monoid N] {x z : M × N} :
    x ~ᵤ z ↔ x.1 ~ᵤ z.1 ∧ x.2 ~ᵤ z.2 := ⟨fun ⟨u, hu⟩ => ⟨⟨(MulEquiv.prodUnits.toFun u).1, (Prod.eq_iff_fst_eq_snd_eq.1 hu).1⟩,
    ⟨(MulEquiv.prodUnits.toFun u).2, (Prod.eq_iff_fst_eq_snd_eq.1 hu).2⟩⟩,
  fun ⟨⟨u₁, h₁⟩, ⟨u₂, h₂⟩⟩ =>
    ⟨MulEquiv.prodUnits.invFun (u₁, u₂), Prod.eq_iff_fst_eq_snd_eq.2 ⟨h₁, h₂⟩⟩⟩

-- TODO: this seems to trigger a bug in the mergeWithGrind linter

