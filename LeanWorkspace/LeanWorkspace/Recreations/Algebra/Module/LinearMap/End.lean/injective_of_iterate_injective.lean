import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]

variable {f' : End R M}

theorem injective_of_iterate_injective {n : ℕ} (hn : n ≠ 0) (h : Function.Injective (f' ^ n)) :
    Function.Injective f' := by
  rw [← Nat.succ_pred_eq_of_pos (show 0 < n by lia), Module.End.iterate_succ, coe_comp] at h
  exact h.of_comp

