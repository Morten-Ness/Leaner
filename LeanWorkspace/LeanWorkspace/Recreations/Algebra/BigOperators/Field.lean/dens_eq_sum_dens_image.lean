import Mathlib

variable {ι K : Type*} [DivisionSemiring K]

variable {α β : Type*} [Fintype β]

variable {s : Finset α} {t : α → Finset β}

theorem dens_eq_sum_dens_image [DecidableEq α] (f : β → α) (t : Finset β) :
    t.dens = ∑ a ∈ t.image f, {b ∈ t | f b = a}.dens := Finset.dens_eq_sum_dens_fiberwise fun _ ↦ mem_image_of_mem _

