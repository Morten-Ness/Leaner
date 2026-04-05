import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem prod_hom_nonempty {l : List M} {F : Type*} [FunLike F M N] [MulHomClass F M N] (f : F)
    (hl : l ≠ []) : (l.map f).prod = f l.prod := match l, hl with | x :: xs, hl => by induction xs generalizing x <;> simp_all

