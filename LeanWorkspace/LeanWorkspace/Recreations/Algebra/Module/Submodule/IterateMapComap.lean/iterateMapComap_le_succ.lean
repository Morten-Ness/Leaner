import Mathlib

variable {R N M : Type*} [Semiring R] [AddCommMonoid N] [Module R N]
  [AddCommMonoid M] [Module R M] (f i : N →ₗ[R] M)

theorem iterateMapComap_le_succ (K : Submodule R N) (h : K.map f ≤ K.map i) (n : ℕ) :
    f.iterateMapComap i n K ≤ f.iterateMapComap i (n + 1) K := by
  nth_rw 2 [LinearMap.iterateMapComap]
  rw [iterate_succ', Function.comp_apply, ← LinearMap.iterateMapComap, ← map_le_iff_le_comap]
  induction n with
  | zero => exact h
  | succ n ih =>
    simp_rw [LinearMap.iterateMapComap, iterate_succ', Function.comp_apply]
    calc
      _ ≤ (f.iterateMapComap i n K).map i := map_comap_le _ _
      _ ≤ (((f.iterateMapComap i n K).map f).comap f).map i := by grw [← le_comap_map]
      _ ≤ _ := by gcongr; exact ih

