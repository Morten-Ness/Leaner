import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

theorem eq_zero_of_isNilpotent_ad_of_mem_isCartanSubalgebra {x : L} (hx : x ∈ H)
    (hx' : _root_.IsNilpotent (ad K L x)) : x = 0 := by
  suffices ⟨x, hx⟩ ∈ LinearMap.ker (traceForm K H L) by
    simp only [ker_traceForm_eq_bot_of_isCartanSubalgebra, Submodule.mem_bot] at this
    exact (AddSubmonoid.mk_eq_zero H.toAddSubmonoid).mp this
  simp only [LinearMap.mem_ker]
  ext y
  have comm : Commute (toEnd K H L ⟨x, hx⟩) (toEnd K H L y) := by
    rw [commute_iff_lie_eq, ← LieHom.map_lie, trivial_lie_zero, map_zero]
  rw [traceForm_apply_apply, ← Module.End.mul_eq_comp, LinearMap.zero_apply]
  exact (LinearMap.isNilpotent_trace_of_isNilpotent (comm.isNilpotent_mul_right hx')).eq_zero

