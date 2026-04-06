FAIL
import Mathlib

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_hom_ne_zero {s : Multiset M} (hs : s ≠ 0) {F : Type*} [FunLike F M N]
    [MulHomClass F M N] (f : F) :
    (s.map f).prod = f s.prod := by
  induction s using Multiset.induction_on with
  | empty =>
      contradiction
  | @cons a s ih =>
      simp [ih (Multiset.cons_ne_zero _ _), map_mul]
