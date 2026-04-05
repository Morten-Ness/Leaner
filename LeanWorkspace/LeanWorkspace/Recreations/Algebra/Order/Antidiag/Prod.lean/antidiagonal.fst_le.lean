import Mathlib

variable {A : Type*}

variable [AddCommMonoid A] [PartialOrder A] [CanonicallyOrderedAdd A] [HasAntidiagonal A]

theorem antidiagonal.fst_le {n : A} {kl : A × A} (hlk : kl ∈ antidiagonal n) : kl.1 ≤ n := by
  rw [le_iff_exists_add]
  use kl.2
  rwa [mem_antidiagonal, eq_comm] at hlk

