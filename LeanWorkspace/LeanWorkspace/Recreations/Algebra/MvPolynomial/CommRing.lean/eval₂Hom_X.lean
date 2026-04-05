import Mathlib

variable {R : Type u} {S : Type v}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommRing R]

variable {p q : MvPolynomial σ R}

variable [CommRing S]

variable (f : R →+* S) (g : σ → S)

theorem eval₂Hom_X {R : Type u} (c : ℤ →+* S) (f : MvPolynomial R ℤ →+* S) (x : MvPolynomial R ℤ) :
    eval₂ c (f ∘ X) x = f x := by
  apply MvPolynomial.induction_on x
    (fun n => by
      rw [MvPolynomial.hom_C f, eval₂_C]
      exact eq_intCast c n)
    (fun p q hp hq => by
      rw [eval₂_add, hp, hq]
      exact (f.map_add _ _).symm)
    (fun p n hp => by
      rw [eval₂_mul, eval₂_X, hp]
      exact (f.map_mul _ _).symm)

