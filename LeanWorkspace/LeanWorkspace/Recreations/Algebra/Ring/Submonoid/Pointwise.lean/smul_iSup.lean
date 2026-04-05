import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [AddMonoid R] [AddMonoid A] [DistribSMul R A]

variable {M M' : AddSubmonoid R} {N P : AddSubmonoid A} {m : R} {n : A}

variable {ι : Sort*}

theorem smul_iSup (T : AddSubmonoid R) (S : ι → AddSubmonoid A) : (T • ⨆ i, S i) = ⨆ i, T • S i := le_antisymm (AddSubmonoid.smul_le.mpr fun t ht s hs ↦ iSup_induction _ (motive := (t • · ∈ _)) hs
    (fun i s hs ↦ mem_iSup_of_mem i <| AddSubmonoid.smul_mem_smul ht hs)
    (by simp_rw [smul_zero]; apply zero_mem) fun x y ↦ by simp_rw [smul_add]; apply add_mem)
  (iSup_le fun i ↦ AddSubmonoid.smul_le_smul_right <| le_iSup _ i)

