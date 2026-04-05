import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [CommSemiring R] {p : R[X]}

theorem monic_finprod_of_monic (α : Type*) (f : α → R[X])
    (hf : ∀ i ∈ Function.mulSupport f, Polynomial.Monic (f i)) :
    Polynomial.Monic (finprod f) := by
  classical
  rw [finprod_def]
  split_ifs
  · exact Polynomial.monic_prod_of_monic _ _ fun a ha => hf a ((Set.Finite.mem_toFinset _).mp ha)
  · exact Polynomial.monic_one

