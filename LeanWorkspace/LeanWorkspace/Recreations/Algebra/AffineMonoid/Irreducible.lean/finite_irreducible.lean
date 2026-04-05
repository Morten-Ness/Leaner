import Mathlib

variable {M : Type*}

variable [CommMonoid M] [Subsingleton Mˣ] {S : Set M}

variable [Monoid.FG M]

theorem finite_irreducible : {p : M | Irreducible p}.Finite := by
  simpa using Monoid.FG.fg_top.finite_irreducible_mem_submonoidClosure

