import Mathlib

variable {ι : Type*}

variable {α β} {A : ι → Type*}

theorem smul_mk [∀ i, SMul α (A i)] {i} (c : α) (a : A i) :
    c • GradedMonoid.mk i a = GradedMonoid.mk i (c • a) := rfl

