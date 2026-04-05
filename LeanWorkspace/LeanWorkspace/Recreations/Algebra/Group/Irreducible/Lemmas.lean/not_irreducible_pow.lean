import Mathlib

variable {F M N : Type*}

variable [Monoid M] [Monoid N] {f : F} {x y : M}

theorem not_irreducible_pow : ∀ {n : ℕ}, n ≠ 1 → ¬ Irreducible (x ^ n)
  | 0, _ => by simp
  | n + 2, _ => by
    intro ⟨h₁, h₂⟩
    have := h₂ (pow_succ _ _)
    rw [isUnit_pow_iff n.succ_ne_zero, or_self] at this
    exact h₁ (this.pow _)

