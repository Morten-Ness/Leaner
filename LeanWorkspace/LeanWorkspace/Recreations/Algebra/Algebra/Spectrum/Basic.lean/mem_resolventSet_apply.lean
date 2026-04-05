import Mathlib

open scoped Pointwise Ring

variable {F R A B : Type*} [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

variable [FunLike F A B] [AlgHomClass F R A B]

theorem mem_resolventSet_apply (φ : F) {a : A} {r : R} (h : r ∈ resolventSet R a) :
    r ∈ resolventSet R ((φ : A → B) a) := by
  simpa only [map_sub, AlgHomClass.commutes] using h.map φ

