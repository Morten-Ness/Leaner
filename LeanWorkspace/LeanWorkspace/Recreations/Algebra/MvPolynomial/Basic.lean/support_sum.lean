import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem support_sum {α : Type*} [DecidableEq σ] {s : Finset α} {f : α → MvPolynomial σ R} :
    (∑ x ∈ s, f x).support ⊆ s.biUnion fun x => (f x).support := Finsupp.support_finset_sum

