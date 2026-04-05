import Mathlib

variable {ι K : Type*} [DivisionSemiring K]

variable {α β : Type*} [Fintype β]

variable {s : Finset α} {t : α → Finset β}

theorem dens_biUnion_le [DecidableEq β] : (s.biUnion t).dens ≤ ∑ a ∈ s, (t a).dens := by
  simp only [dens, ← sum_div]
  gcongr
  exact mod_cast card_biUnion_le

