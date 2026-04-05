import Mathlib

variable {ι α : Type*} {R : ι → Type*}

theorem isSMulRegular_iff [∀ i, SMul α (R i)] {r : α} [∀ i, Nonempty (R i)] :
    IsSMulRegular (∀ i, R i) r ↔ ∀ i, IsSMulRegular (R i) r := Pi.map_injective

