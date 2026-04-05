import Mathlib

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_add (s t : Multiset M) : prod (s + t) = prod s * prod t := Quotient.inductionOn₂ s t fun l₁ l₂ => by simp [List.prod_append]

