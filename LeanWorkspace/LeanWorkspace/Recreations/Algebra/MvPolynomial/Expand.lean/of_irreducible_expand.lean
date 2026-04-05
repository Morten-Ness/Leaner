import Mathlib

variable (R σ : Type*) [CommRing R]

theorem of_irreducible_expand {p : ℕ} (hp : p ≠ 0) {f : MvPolynomial σ R}
    (hf : Irreducible (MvPolynomial.expand p f)) :
    Irreducible f := let _ := MvPolynomial.isLocalHom_expand R σ hp
  hf.of_map

