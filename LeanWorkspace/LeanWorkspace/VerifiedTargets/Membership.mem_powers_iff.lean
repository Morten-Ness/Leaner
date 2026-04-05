import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem mem_powers_iff (x z : M) : x ∈ Submonoid.powers z ↔ ∃ n : ℕ, z ^ n = x := Iff.rfl

noncomputable instance decidableMemPowers : DecidablePred (· ∈ Submonoid.powers a) :=
  Classical.decPred _

-- TODO the following instance should follow from a more general principle
-- See also https://github.com/leanprover-community/mathlib4/issues/2417
noncomputable instance fintypePowers [Fintype M] : Fintype (Submonoid.powers a) :=
  inferInstanceAs <| Fintype {y // y ∈ Submonoid.powers a}

