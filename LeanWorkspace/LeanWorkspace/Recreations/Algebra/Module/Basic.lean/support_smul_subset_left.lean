import Mathlib

variable {α R M M₂ : Type*}

theorem support_smul_subset_left [Zero R] [Zero M] [SMulWithZero R M] (f : α → R) (g : α → M) :
    support (f • g) ⊆ support f := fun x hfg hf ↦
  hfg <| by rw [Pi.smul_apply', hf, zero_smul]

-- Changed (2024-01-21): this lemma was generalised;
-- the old version is now called `support_const_smul_subset`.

