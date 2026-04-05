import Mathlib

open scoped Pointwise

variable {R : Type*} [CommRing R]

variable {K : Type*} [Field K] [Algebra R K]

theorem _root_.Submodule.span_range_eq_top_of_injective_of_rank_le {M N : Type u} [IsDomain R]
    [IsFractionRing R K] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module K N] [IsScalarTower R K N] [Module.Finite K N]
    {f : M →ₗ[R] N} (hf : Function.Injective f) (h : Module.rank K N ≤ Module.rank R M) :
    Submodule.span K (LinearMap.range f : Set N) = ⊤ := by
  obtain ⟨s, hs, hli⟩ := exists_set_linearIndependent R M
  replace hli := hli.map' f (LinearMap.ker_eq_bot.mpr hf)
  rw [LinearIndependent.iff_fractionRing (R := R) (K := K)] at hli
  replace hs : Cardinal.mk s = Module.rank K N :=
    le_antisymm (LinearIndependent.cardinal_le_rank hli) (hs ▸ h)
  rw [← Module.finrank_eq_rank, Cardinal.mk_eq_nat_iff_fintype] at hs
  obtain ⟨hfin, hcard⟩ := hs
  have hsubset : Set.range (fun x : s ↦ f x.val) ⊆ (LinearMap.range f : Set N) := by
    rintro x ⟨a, rfl⟩
    simp
  rw [eq_top_iff, ← LinearIndependent.span_eq_top_of_card_eq_finrank' hli hcard]
  exact Submodule.span_mono hsubset

