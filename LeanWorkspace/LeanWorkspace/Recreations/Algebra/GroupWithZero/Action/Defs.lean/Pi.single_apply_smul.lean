import Mathlib

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable (M₀ A) [MonoidWithZero M₀] [MonoidWithZero M₀'] [Zero A]

variable {M₀ A} [MulActionWithZero M₀ A] [Zero A'] [SMul M₀ A'] (p : Prop) [Decidable p]

theorem Pi.single_apply_smul {ι : Type*} [DecidableEq ι] (x : A) (i j : ι) :
    (Pi.single i 1 : ι → M₀) j • x = (Pi.single i x : ι → A) j := by
  rw [single_apply, ite_smul, one_smul, zero_smul, single_apply]

