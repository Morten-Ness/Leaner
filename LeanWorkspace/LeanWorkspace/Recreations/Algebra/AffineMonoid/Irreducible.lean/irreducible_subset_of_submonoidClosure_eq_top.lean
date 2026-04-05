import Mathlib

variable {M : Type*}

variable [CommMonoid M] [Subsingleton Mˣ] {S : Set M}

theorem irreducible_subset_of_submonoidClosure_eq_top (hS : Submonoid.closure S = ⊤) :
    {p | Irreducible p} ⊆ S := by
  simpa [hS] using irreducible_mem_submonoidClosure_subset (S := S)

