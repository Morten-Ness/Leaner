import Mathlib

variable {R S : Type*} (n : Type*) [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]

variable (f : R →+* S)

theorem univ_map_eval₂Hom (M : n × n → S) :
    (univ R n).map (eval₂Hom f M) = Matrix.charpoly (Matrix.of M.curry) := by
  rw [univ, ← charpoly_map, coe_eval₂Hom, ← mvPolynomialX_map_eval₂ f (Matrix.of M.curry)]
  simp only [of_apply, Function.curry_apply, Prod.mk.eta]

