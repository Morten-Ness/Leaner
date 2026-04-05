import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem FG.generators_ncard {p : Submodule R M} (h : p.FG) :
    (Submodule.generators p).ncard = Submodule.spanFinrank p := by
  rw [← Nat.cast_inj (R := Cardinal), ← Submodule.fg_iff_spanRank_eq_spanFinrank.mpr h, Set.ncard, Set.encard,
     ENat.card, Submodule.generators_card, toNat_toENat, ← Submodule.spanFinrank]
  exact (Submodule.fg_iff_spanRank_eq_spanFinrank.mpr h).symm

