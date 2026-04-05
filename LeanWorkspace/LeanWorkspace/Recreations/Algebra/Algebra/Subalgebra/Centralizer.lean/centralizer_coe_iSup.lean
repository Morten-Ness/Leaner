import Mathlib

variable {R : Type*} [CommSemiring R]

variable {A : Type*} [Semiring A] [Algebra R A]

theorem centralizer_coe_iSup {ι : Sort*} (S : ι → Subalgebra R A) :
    centralizer R ((⨆ i, S i : Subalgebra R A) : Set A) = ⨅ i, centralizer R (S i) := eq_of_forall_le_iff fun K ↦ by
    simp_rw [Subalgebra.le_centralizer_iff, iSup_le_iff, le_iInf_iff, K.le_centralizer_iff]

