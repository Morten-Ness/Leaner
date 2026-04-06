FAIL
import Mathlib

open scoped Pointwise Ring

variable {F R A B : Type*} [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

variable [FunLike F A B] [AlgHomClass F R A B]

theorem mem_resolventSet_apply (φ : F) {a : A} {r : R} (h : r ∈ resolventSet R a) :
    r ∈ resolventSet R ((φ : A → B) a) := by
  rw [resolventSet, Set.mem_setOf_eq] at h ⊢
  let ψ : A →+* B := AlgHomClass.toAlgHom φ.toRingHom
  have hmap := IsUnit.map ψ h
  simpa [map_sub, AlgHomClass.commutes] using hmap
