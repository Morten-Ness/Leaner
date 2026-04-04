import Mathlib

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem sub_div_sub_smul_slope_add_sub_div_sub_smul_slope (f : k → PE) (a b c : k) :
    ((b - a) / (c - a)) • slope f a b + ((c - b) / (c - a)) • slope f b c = slope f a c := by
  by_cases hab : a = b
  · subst hab
    rw [sub_self, zero_div, zero_smul, zero_add]
    by_cases hac : a = c
    · simp [hac]
    · rw [div_self (sub_ne_zero.2 <| Ne.symm hac), one_smul]
  by_cases hbc : b = c
  · subst hbc
    simp [sub_ne_zero.2 (Ne.symm hab)]
  rw [add_comm]
  simp_rw [slope, div_eq_inv_mul, mul_smul, ← smul_add,
    smul_inv_smul₀ (sub_ne_zero.2 <| Ne.symm hab), smul_inv_smul₀ (sub_ne_zero.2 <| Ne.symm hbc),
    vsub_add_vsub_cancel]

