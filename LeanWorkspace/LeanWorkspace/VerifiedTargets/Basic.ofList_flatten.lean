import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem ofList_flatten (xs : List (List α)) : FreeMonoid.ofList xs.flatten = (xs.map FreeMonoid.ofList).prod := FreeMonoid.toList.injective <| by simp

