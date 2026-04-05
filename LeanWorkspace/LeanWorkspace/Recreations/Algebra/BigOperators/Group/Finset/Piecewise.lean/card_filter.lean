import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

theorem card_filter (p) [DecidablePred p] (s : Finset ι) :
    #{i ∈ s | p i} = ∑ i ∈ s, ite (p i) 1 0 := by simp [sum_ite]

