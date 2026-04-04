import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

variable (P) in

theorem mem_spanPoints (p : P) (s : Set P) : p ∈ s → p ∈ spanPoints k s
  | hp => ⟨p, hp, 0, Submodule.zero_mem _, (zero_vadd V p).symm⟩
