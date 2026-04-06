import Mathlib

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_eq_one (h : ∀ x ∈ s, x = (1 : M)) : s.prod = 1 := by
  classical
  revert h
  refine Multiset.induction_on s ?_ ?_
  · intro h
    simp
  · intro a s ih h
    have ha : a = (1 : M) := h a (by simp)
    have hs : ∀ x ∈ s, x = (1 : M) := by
      intro x hx
      exact h x (by simp [hx])
    simp [ha, ih hs]
