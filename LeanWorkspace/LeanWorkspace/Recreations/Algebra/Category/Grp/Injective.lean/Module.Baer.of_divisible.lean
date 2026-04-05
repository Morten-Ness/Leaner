import Mathlib

variable (A : Type u) [AddCommGroup A]

theorem Module.Baer.of_divisible [DivisibleBy A ℤ] : Module.Baer ℤ A := fun I g ↦ by
  rcases IsPrincipalIdealRing.principal I with ⟨m, rfl⟩
  obtain rfl | h0 := eq_or_ne m 0
  · refine ⟨0, fun n hn ↦ ?_⟩
    rw [Submodule.span_zero_singleton] at hn
    subst hn
    exact (map_zero g).symm
  let gₘ := g ⟨m, Submodule.subset_span (Set.mem_singleton _)⟩
  refine ⟨LinearMap.toSpanSingleton ℤ A (DivisibleBy.div gₘ m), fun n hn ↦ ?_⟩
  rcases Submodule.mem_span_singleton.mp hn with ⟨n, rfl⟩
  rw [map_zsmul, LinearMap.toSpanSingleton_apply, DivisibleBy.div_cancel gₘ h0, ← map_zsmul g,
    SetLike.mk_smul_mk]

