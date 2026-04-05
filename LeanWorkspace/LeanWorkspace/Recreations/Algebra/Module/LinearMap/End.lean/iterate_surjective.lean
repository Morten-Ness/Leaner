import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]

variable {f' : End R M}

theorem iterate_surjective (h : Function.Surjective f') : ∀ n : ℕ, Function.Surjective (f' ^ n)
  | 0 => surjective_id
  | n + 1 => by
    rw [Module.End.iterate_succ]
    exact (iterate_surjective h n).comp h
