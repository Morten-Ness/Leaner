import Mathlib

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem dvd_prod : a ∈ s → a ∣ s.prod := Quotient.inductionOn s (fun l a h ↦ by simpa using List.dvd_prod h) a

