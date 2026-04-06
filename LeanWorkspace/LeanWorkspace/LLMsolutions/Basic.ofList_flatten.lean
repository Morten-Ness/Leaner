import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem ofList_flatten (xs : List (List α)) : FreeMonoid.ofList xs.flatten = (xs.map FreeMonoid.ofList).prod := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, FreeMonoid.ofList_append, List.flatten]
