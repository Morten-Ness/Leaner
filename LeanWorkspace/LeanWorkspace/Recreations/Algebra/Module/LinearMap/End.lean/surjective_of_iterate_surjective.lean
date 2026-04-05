import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]

variable {f' : End R M}

theorem surjective_of_iterate_surjective {n : ℕ} (hn : n ≠ 0) (h : Function.Surjective (f' ^ n)) :
    Function.Surjective f' := by
  rw [← Nat.succ_pred_eq_of_pos (Nat.pos_iff_ne_zero.mpr hn), pow_succ', Module.End.coe_mul] at h
  exact Function.Surjective.of_comp h

