import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]

variable {f' : End R M}

theorem iterate_bijective (h : Function.Bijective f') : ∀ n : ℕ, Function.Bijective (f' ^ n)
  | 0 => bijective_id
  | n + 1 => by
    rw [Module.End.iterate_succ]
    exact (iterate_bijective h n).comp h
