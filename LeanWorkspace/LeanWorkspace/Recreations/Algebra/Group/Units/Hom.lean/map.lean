import Mathlib

variable {F G M N : Type*} [FunLike F M N] [FunLike G N M]

variable [Monoid M] [Monoid N]

theorem map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : IsUnit (f x) := by
  rcases h with ⟨y, rfl⟩; exact (Units.map (f : M →* N) y).isUnit

