import Mathlib

variable {ι K : Type*} [DivisionSemiring K]

variable {α β : Type*} [Fintype β]

variable {s : Finset α} {t : α → Finset β}

theorem dens_eq_sum_dens_fiberwise [DecidableEq α] {f : β → α} {t : Finset β}
    (h : (t : Set β).MapsTo f s) : t.dens = ∑ a ∈ s, {b ∈ t | f b = a}.dens := by
  simp [dens, ← sum_div, card_eq_sum_card_fiberwise h]

