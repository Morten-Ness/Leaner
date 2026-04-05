import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable {S subS : Type*} [CommSemiring S] [SetLike subS S] [SubsemiringClass subS S]

theorem eval₂_mem {f : R →+* S} {p : MvPolynomial σ R} {s : subS}
    (hs : ∀ i ∈ p.support, f (p.coeff i) ∈ s) {v : σ → S} (hv : ∀ i, v i ∈ s) :
    MvPolynomial.eval₂ f v p ∈ s := by
  classical
  replace hs : ∀ i, f (p.coeff i) ∈ s := by
    intro i
    by_cases hi : i ∈ p.support
    · exact hs i hi
    · rw [MvPolynomial.notMem_support_iff.1 hi, f.map_zero]
      exact zero_mem s
  induction p using MvPolynomial.monomial_add_induction_on with
  | C a =>
    simpa using hs 0
  | monomial_add a b f ha _ ih =>
    rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_monomial]
    refine add_mem (mul_mem ?_ <| prod_mem fun i _ => pow_mem (hv _) _) (ih fun i => ?_)
    · simpa [MvPolynomial.notMem_support_iff.1 ha] using hs a
    have := hs i
    rw [coeff_add, coeff_monomial] at this
    split_ifs at this with h
    · subst h
      rw [MvPolynomial.notMem_support_iff.1 ha, map_zero]
      exact zero_mem _
    · rwa [zero_add] at this

