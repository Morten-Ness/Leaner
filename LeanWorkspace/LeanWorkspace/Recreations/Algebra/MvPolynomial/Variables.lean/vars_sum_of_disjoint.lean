import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

variable {ι : Type*} (t : Finset ι) (φ : ι → MvPolynomial σ R)

theorem vars_sum_of_disjoint [DecidableEq σ] (h : Pairwise <| (Disjoint on fun i => (φ i).vars)) :
    (∑ i ∈ t, φ i).vars = Finset.biUnion t fun i => (φ i).vars := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert _ _ has hsum =>
    rw [Finset.biUnion_insert, Finset.sum_insert has, MvPolynomial.vars_add_of_disjoint, hsum]
    unfold Pairwise onFun at h
    simp only [Finset.disjoint_iff_ne] at h ⊢
    grind

