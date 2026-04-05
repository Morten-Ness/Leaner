import Mathlib

variable {R N M : Type*} [Semiring R] [AddCommMonoid N] [Module R N]
  [AddCommMonoid M] [Module R M] (f i : N →ₗ[R] M)

theorem iterateMapComap_eq_succ (K : Submodule R N)
    (m : ℕ) (heq : f.iterateMapComap i m K = f.iterateMapComap i (m + 1) K)
    (hf : Function.Surjective f) (hi : Function.Injective i) (n : ℕ) :
    f.iterateMapComap i n K = f.iterateMapComap i (n + 1) K := by
  induction n with
  | zero =>
    contrapose! heq
    induction m with
    | zero => exact heq
    | succ m ih =>
      rw [LinearMap.iterateMapComap, LinearMap.iterateMapComap, iterate_succ', iterate_succ']
      exact fun H ↦ ih (map_injective_of_injective hi (comap_injective_of_surjective hf H))
  | succ n ih =>
    rw [LinearMap.iterateMapComap, LinearMap.iterateMapComap, iterate_succ', iterate_succ',
      Function.comp_apply, Function.comp_apply, ← LinearMap.iterateMapComap, ← LinearMap.iterateMapComap, ih]

