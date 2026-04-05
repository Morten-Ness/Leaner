import Mathlib

open scoped Polynomial

variable (R : Type u) [CommRing R] [IsDomain R]

theorem of_irreducible_expand {p : ℕ} (hp : p ≠ 0) {f : R[X]} (hf : Irreducible (Polynomial.expand R p f)) :
    Irreducible f := let _ := Polynomial.isLocalHom_expand R hp.bot_lt
  hf.of_map

