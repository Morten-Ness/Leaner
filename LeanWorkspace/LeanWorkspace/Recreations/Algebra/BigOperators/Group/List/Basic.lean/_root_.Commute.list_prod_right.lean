import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem _root_.Commute.list_prod_right (l : List M) (y : M) (h : ∀ x ∈ l, Commute y x) :
    Commute y l.prod := by
  induction l with
  | nil => simp
  | cons z l IH =>
    rw [List.forall_mem_cons] at h
    rw [List.prod_cons]
    exact Commute.mul_right h.1 (IH h.2)

