import Mathlib

variable {R N M : Type*} [Semiring R] [AddCommMonoid N] [Module R N]
  [AddCommMonoid M] [Module R M] (f i : N →ₗ[R] M)

theorem ker_le_of_iterateMapComap_eq_succ (K : Submodule R N)
    (m : ℕ) (heq : f.iterateMapComap i m K = f.iterateMapComap i (m + 1) K)
    (hf : Function.Surjective f) (hi : Function.Injective i) : LinearMap.ker f ≤ K := by
  rw [show K = _ from LinearMap.iterateMapComap_eq_succ f i K m heq hf hi 0]
  exact f.ker_le_comap

