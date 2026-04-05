import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M] [Fintype ι]

theorem prod_ite_eq_ite_exists (p : ι → Prop) [DecidablePred p] (h : ∀ i j, p i → p j → i = j)
    (a : M) : ∏ i, ite (p i) a 1 = ite (∃ i, p i) a 1 := by
  simp [Finset.prod_ite_one Finset.univ p (by simpa using h)]

