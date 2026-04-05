import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem closure_eq_one_union (s : Set M) :
    Submonoid.closure s = {(1 : M)} ∪ (Subsemigroup.closure s : Set M) := by
  apply le_antisymm
  · intro x hx
    induction hx using Submonoid.closure_induction with
    | mem x hx => exact Or.inr <| Subsemigroup.subset_closure hx
    | one => exact Or.inl <| by simp
    | mul x hx y hy hx hy =>
      push _ ∈ _ at hx hy
      obtain ⟨(rfl | hx), (rfl | hy)⟩ := And.intro hx hy
      all_goals simp_all [mul_mem]
  · rintro x (hx | hx)
    · exact (show x = 1 by simpa using hx) ▸ one_mem (Submonoid.closure s)
    · exact Subsemigroup.closure_le.mpr Submonoid.subset_closure hx

