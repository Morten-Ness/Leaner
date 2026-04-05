import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsTriangularizable K H L]

theorem mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg
    {α : H → K} {x : L} (hx : x ∈ rootSpace H α)
    (hx' : ∀ y ∈ rootSpace H (-α), killingForm K L x y = 0) :
    x ∈ LinearMap.ker (killingForm K L) := by
  rw [LinearMap.mem_ker]
  ext y
  have hy : y ∈ ⨆ β, rootSpace H β := by simp [iSup_genWeightSpace_eq_top K H L]
  induction hy using LieSubmodule.iSup_induction' with
  | mem β y hy =>
    by_cases hαβ : α + β = 0
    · exact hx' _ (add_eq_zero_iff_neg_eq.mp hαβ ▸ hy)
    · exact LieAlgebra.killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero K L H hx hy hαβ
  | zero => simp
  | add => simp_all

