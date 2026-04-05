import Mathlib

open scoped Finset

variable {ι κ M N R α : Type*}

variable [CommMonoid M] [CommMonoid N] {s : Finset ι} {f : ι → M × N}

theorem fst_prod : (∏ c ∈ s, f c).1 = ∏ c ∈ s, (f c).1 := map_prod (MonoidHom.fst ..) f s

