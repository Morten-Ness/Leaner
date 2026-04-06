FAIL
import Mathlib

variable {α : Type u} {β : Type v}

variable [CommMonoid α]

theorem mk_injective : Function.Injective (@ConjClasses.mk α _) := by
  intro a b h
  rw [← ConjClasses.eq_iff] at h
  simpa using h
