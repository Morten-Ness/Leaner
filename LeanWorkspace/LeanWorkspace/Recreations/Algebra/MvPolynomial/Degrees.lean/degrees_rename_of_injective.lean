import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degrees_rename_of_injective {p : MvPolynomial σ R} {f : σ → τ} (h : Function.Injective f) :
    MvPolynomial.degrees (rename f p) = (MvPolynomial.degrees p).map f := by
  classical
  simp only [MvPolynomial.degrees, Multiset.map_finset_sup p.support Finsupp.toMultiset f h,
    support_rename_of_injective h, Finset.sup_image]
  refine Finset.sup_congr rfl fun x _ => ?_
  exact (Finsupp.toMultiset_map _ _).symm

