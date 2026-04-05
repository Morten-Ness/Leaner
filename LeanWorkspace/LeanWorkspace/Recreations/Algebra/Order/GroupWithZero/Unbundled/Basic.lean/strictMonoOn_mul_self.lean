import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [PartialOrder M₀] {a b c d : M₀} {m n : ℕ}

theorem strictMonoOn_mul_self [PosMulStrictMono M₀] [MulPosMono M₀] :
    StrictMonoOn (fun x ↦ x * x) {x : M₀ | 0 ≤ x} := fun _ hx _ _ hxy ↦ mul_self_lt_mul_self hx hxy

-- See Note [decidable namespace]
protected lemma Decidable.mul_lt_mul'' [PosMulMono M₀] [PosMulStrictMono M₀] [MulPosStrictMono M₀]
    [DecidableLE M₀] (h1 : a < c) (h2 : b < d) (h3 : 0 ≤ a) (h4 : 0 ≤ b) : a * b < c * d :=
  h4.lt_or_eq_dec.elim (fun b0 ↦ mul_lt_mul h1 h2.le b0 <| h3.trans h1.le) fun b0 ↦ by
    rw [← b0, mul_zero]; exact mul_pos (h3.trans_lt h1) (h4.trans_lt h2)

