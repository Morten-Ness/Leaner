import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M] [Fintype ι]

theorem prod_ite_eq_ite_exists (p : ι → Prop) [DecidablePred p] (h : ∀ i j, p i → p j → i = j)
    (a : M) : ∏ i, ite (p i) a 1 = ite (∃ i, p i) a 1 := by
  classical
  by_cases hex : ∃ i, p i
  · have hright : ite (∃ i, p i) a 1 = a := by simp [hex]
    rw [hright]
    rcases hex with ⟨i, hi⟩
    have hunique : ∀ j, p j ↔ j = i := by
      intro j
      constructor
      · intro hj
        exact h j i hj hi
      · intro hji
        simpa [hji] using hi
    calc
      ∏ j, ite (p j) a 1 = ∏ j, ite (j = i) a 1 := by
        refine Finset.prod_congr rfl ?_
        intro j hj
        simp [hunique j]
      _ = a := by
        simpa using Fintype.prod_ite_eq' (f := fun _ : ι => a) i
  · have hright : ite (∃ i, p i) a 1 = (1 : M) := by simp [hex]
    rw [hright]
    have hnone : ∀ i, ¬ p i := by
      intro i hi
      exact hex ⟨i, hi⟩
    calc
      ∏ i, ite (p i) a 1 = ∏ i, (1 : M) := by
        refine Finset.prod_congr rfl ?_
        intro i hi
        simp [hnone i]
      _ = 1 := by simp
