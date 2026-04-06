import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem monotone_comap {f : F} : Monotone (Submonoid.comap f) := by
  intro S T hST
  show Submonoid.comap f S ≤ Submonoid.comap f T
  intro x hx
  exact hST hx
