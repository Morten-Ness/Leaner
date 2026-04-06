import Mathlib

variable {ι M N : Type*}

variable [Monoid M] [Monoid N]

theorem prod_eq_pow_card (l : List M) (m : M) (h : ∀ x ∈ l, x = m) : l.prod = m ^ l.length := by
  induction l with
  | nil =>
      simp
  | cons a l ih =>
      have ha : a = m := h a (by simp)
      have hl : ∀ x ∈ l, x = m := by
        intro x hx
        exact h x (by simp [hx])
      rw [List.prod_cons, ha, ih hl, List.length_cons, pow_succ']
