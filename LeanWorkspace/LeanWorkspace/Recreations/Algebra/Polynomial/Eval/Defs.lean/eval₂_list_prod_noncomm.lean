import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S) (x : S)

variable [Semiring T]

theorem eval₂_list_prod_noncomm (ps : List R[X])
    (hf : ∀ p ∈ ps, ∀ (k), Commute (f <| coeff p k) x) :
    eval₂ f x ps.prod = (ps.map (Polynomial.eval₂ f x)).prod := by
  induction ps using List.reverseRecOn with
  | nil => simp
  | append_singleton ps p ihp =>
    simp only [List.forall_mem_append, List.forall_mem_singleton] at hf
    simp [Polynomial.eval₂_mul_noncomm _ _ hf.2, ihp hf.1]

