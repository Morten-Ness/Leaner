import Mathlib

variable {ι K : Type*} [DivisionSemiring K]

variable {α β : Type*} [Fintype β]

theorem dens_disjiUnion (s : Finset α) (t : α → Finset β) (h) :
    (s.disjiUnion t h).dens = ∑ a ∈ s, (t a).dens := by
  simp [dens, sum_div]

