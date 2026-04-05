import Mathlib

variable {ι α β M N P G : Type*}

variable [CommMonoid M] {a : M} {l l₁ l₂ : List M}

theorem CommMonoid.mul_prod_eraseIdx {i} (h : i < l.length) : l[i] * (l.eraseIdx i).prod = l.prod := List.mul_prod_eraseIdx h (fun a' _ ↦ Commute.all l[i] a')

