import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

variable (f : R →+* S) (k : σ → τ) (g : τ → S) (p : MvPolynomial σ R)

theorem eval_rename_prod_mk (g : σ × τ → R) (i : σ) (p : MvPolynomial τ R) :
    eval g (MvPolynomial.rename (Prod.mk i) p) = eval (fun j => g (i, j)) p := MvPolynomial.eval₂_rename_prod_mk (RingHom.id _) _ _ _

