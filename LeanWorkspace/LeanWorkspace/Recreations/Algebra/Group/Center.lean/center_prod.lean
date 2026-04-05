import Mathlib

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem center_prod {N : Type*} [Mul N] :
    Set.center (M × N) = Set.center M ×ˢ Set.center N := by
  aesop (add simp [Prod.forall, forall_and, commute_iff_eq, isMulCentral_iff, Set.mem_center_iff])

