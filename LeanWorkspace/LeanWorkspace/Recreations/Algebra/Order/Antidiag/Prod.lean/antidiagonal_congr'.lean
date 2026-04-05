import Mathlib

variable {A : Type*}

variable [AddCancelCommMonoid A] [HasAntidiagonal A] {p q : A × A} {n : A}

theorem antidiagonal_congr' (hp : p ∈ antidiagonal n) (hq : q ∈ antidiagonal n) :
    p = q ↔ p.2 = q.2 := by
  rw [← Prod.swap_inj]
  exact Finset.antidiagonal_congr (Finset.swap_mem_antidiagonal.2 hp) (Finset.swap_mem_antidiagonal.2 hq)

