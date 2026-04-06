FAIL
import Mathlib

variable {ι κ M M₀ R : Type*}

variable [NonUnitalNonAssocSemiring R]

theorem list_sum_left (b : R) (l : List R) (h : ∀ a ∈ l, Commute a b) : Commute l.sum b := by
  induction l with
  | nil =>
      simp
  | cons a t ih =>
      have ha : Commute a b := h a (by simp)
      have ht : ∀ x ∈ t, Commute x b := by
        intro x hx
        exact h x (by simp [hx])
      have hs : Commute t.sum b := ih ht
      rw [List.sum_cons]
      exact ha.add_right hs
