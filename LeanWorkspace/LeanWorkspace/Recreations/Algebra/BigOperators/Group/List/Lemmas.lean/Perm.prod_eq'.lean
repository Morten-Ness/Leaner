import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem Perm.prod_eq' (h : l₁ ~ l₂) (hc : l₁.Pairwise Commute) : l₁.prod = l₂.prod := by
  refine h.foldr_eq' ?_ _
  apply Pairwise.forall_of_forall
  · intro x y h z
    exact (h z).symm
  · intros; rfl
  · apply hc.imp
    intro a b h z
    rw [← mul_assoc, ← mul_assoc, h]

