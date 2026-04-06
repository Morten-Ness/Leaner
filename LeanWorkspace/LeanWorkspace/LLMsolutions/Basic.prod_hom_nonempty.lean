FAIL
import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem prod_hom_nonempty {l : List M} {F : Type*} [FunLike F M N] [MulHomClass F M N] (f : F)
    (hl : l ≠ []) : (l.map f).prod = f l.prod := by
  induction l with
  | nil =>
      exfalso
      exact hl rfl
  | cons x xs ih =>
      simp only [List.map, List.prod_cons]
      rw [ih (by simp)]
