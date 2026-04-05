import Mathlib

variable {M : Type*}

variable [CommMonoid M] [Subsingleton Mˣ] {S : Set M}

theorem Submonoid.FG.finite_irreducible_mem_submonoidClosure {S : Submonoid M} (hS : S.FG) :
    {p ∈ S | Irreducible p}.Finite := by
  obtain ⟨T, hT⟩ := hS; exact T.finite_toSet.subset <| hT ▸ irreducible_mem_submonoidClosure_subset

