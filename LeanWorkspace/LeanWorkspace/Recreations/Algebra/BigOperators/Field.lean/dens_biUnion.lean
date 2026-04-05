import Mathlib

variable {ι K : Type*} [DivisionSemiring K]

variable {α β : Type*} [Fintype β]

variable {s : Finset α} {t : α → Finset β}

theorem dens_biUnion [DecidableEq β] (h : (s : Set α).PairwiseDisjoint t) :
    (s.biUnion t).dens = ∑ u ∈ s, (t u).dens := by
  simp [dens, card_biUnion h, sum_div]

