import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem mul_mem_nthRootsFinset
    {η₁ η₂ : R} {a₁ a₂ : R} (hη₁ : η₁ ∈ Polynomial.nthRootsFinset n a₁) (hη₂ : η₂ ∈ Polynomial.nthRootsFinset n a₂) :
    η₁ * η₂ ∈ Polynomial.nthRootsFinset n (a₁ * a₂) := by
  cases n with
  | zero =>
    simp only [Polynomial.nthRootsFinset_zero, notMem_empty] at hη₁
  | succ n =>
    rw [Polynomial.mem_nthRootsFinset n.succ_pos] at hη₁ hη₂ ⊢
    rw [mul_pow, hη₁, hη₂]

