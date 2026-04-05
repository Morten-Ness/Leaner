import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem map_rename (f : R →+* S) (g : σ → τ) (p : MvPolynomial σ R) :
    map f (MvPolynomial.rename g p) = MvPolynomial.rename g (map f p) := by
  apply MvPolynomial.induction_on p
    (fun a => by simp only [map_C, MvPolynomial.rename_C])
    (fun p q hp hq => by simp only [hp, hq, map_add]) fun p n hp => by
    simp only [hp, MvPolynomial.rename_X, map_X, map_mul]

