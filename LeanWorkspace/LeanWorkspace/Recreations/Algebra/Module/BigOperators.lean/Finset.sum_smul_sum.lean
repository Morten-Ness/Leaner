import Mathlib

variable {ι κ α β R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

theorem Finset.sum_smul_sum (s : Finset α) (t : Finset β) {f : α → R} {g : β → M} :
    (∑ i ∈ s, f i) • ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i • g j := by
  simp_rw [sum_smul, ← smul_sum]

