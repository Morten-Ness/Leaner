import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [AddMonoid R] [AddMonoid A] [DistribSMul R A]

variable {M M' : AddSubmonoid R} {N P : AddSubmonoid A} {m : R} {n : A}

theorem addSubmonoid_smul_sup : M • (N ⊔ P) = M • N ⊔ M • P := le_antisymm (AddSubmonoid.smul_le.mpr fun m hm np hnp ↦ by
    refine closure_induction (motive := (fun _ ↦ _ • · ∈ _)) ?_ ?_ ?_ (sup_eq_closure N P ▸ hnp)
    · rintro x (hx | hx)
      exacts [le_sup_left (a := M • N) (AddSubmonoid.smul_mem_smul hm hx),
        le_sup_right (a := M • N) (AddSubmonoid.smul_mem_smul hm hx)]
    · apply (smul_zero (A := A) m).symm ▸ (M • N ⊔ M • P).zero_mem
    · intro _ _ _ _ h1 h2; rw [smul_add]; exact add_mem h1 h2)
  (sup_le (AddSubmonoid.smul_le_smul_right le_sup_left) <| AddSubmonoid.smul_le_smul_right le_sup_right)

