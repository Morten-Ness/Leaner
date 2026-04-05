import Mathlib

open scoped Finset

variable {ι κ M N R α : Type*}

variable [CommMonoid M] [CommMonoid N] {s : Finset ι} {f : ι → M × N}

theorem snd_prod : (∏ c ∈ s, f c).2 = ∏ c ∈ s, (f c).2 := map_prod (MonoidHom.snd ..) f s

