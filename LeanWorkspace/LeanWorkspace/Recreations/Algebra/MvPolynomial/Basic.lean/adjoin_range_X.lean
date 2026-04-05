import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem adjoin_range_X : Algebra.adjoin R (Set.range (MvPolynomial.X : σ → MvPolynomial σ R)) = ⊤ := by
  set S := Algebra.adjoin R (Set.range (MvPolynomial.X : σ → MvPolynomial σ R))
  refine top_unique fun p hp => ?_; clear hp
  induction p using MvPolynomial.induction_on with
  | MvPolynomial.C => exact S.algebraMap_mem _
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p i hp => exact S.mul_mem hp (Algebra.subset_adjoin <| mem_range_self _)

