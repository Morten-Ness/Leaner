import Mathlib

variable {ι α β M N P G : Type*}

variable [CommMonoid M] {a : M} {l l₁ l₂ : List M}

theorem CommMonoid.prod_insertIdx {i} (h : i ≤ l.length) : (l.insertIdx i a).prod = a * l.prod := List.prod_insertIdx h (fun a' _ ↦ Commute.all a a')

