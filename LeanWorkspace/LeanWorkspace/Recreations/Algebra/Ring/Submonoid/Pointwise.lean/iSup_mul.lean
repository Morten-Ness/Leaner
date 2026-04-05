import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [NonUnitalNonAssocSemiring R] {M N P : AddSubmonoid R}

variable {M N P Q : AddSubmonoid R}

variable {ι : Sort*}

theorem iSup_mul (S : ι → AddSubmonoid R) (T : AddSubmonoid R) : (⨆ i, S i) * T = ⨆ i, S i * T := le_antisymm (AddSubmonoid.mul_le.mpr fun s hs t ht ↦ iSup_induction _ (motive := (· * t ∈ _)) hs
      (fun i s hs ↦ mem_iSup_of_mem i <| AddSubmonoid.mul_mem_mul hs ht) (by simp_rw [zero_mul]; apply zero_mem)
      fun _ _ ↦ by simp_rw [right_distrib]; apply add_mem) <|
    iSup_le fun i ↦ AddSubmonoid.mul_le_mul_left (le_iSup _ i)

