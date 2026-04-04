import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem direction_iInf_of_mem (s : ι → AffineSubspace k P) (p : P) (h : ∀ i, p ∈ s i) :
    (iInf s).direction = ⨅ i, (s i).direction := by
  rw [iInf, AffineSubspace.direction_sInf_of_mem _ p ?_, iInf_range]
  rwa [Set.forall_mem_range]

