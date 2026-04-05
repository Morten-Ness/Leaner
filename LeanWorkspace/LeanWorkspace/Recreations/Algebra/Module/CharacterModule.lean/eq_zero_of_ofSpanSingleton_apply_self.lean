import Mathlib

variable (R : Type uR) [CommRing R]

variable (A : Type uA) [AddCommGroup A]

variable (A' : Type*) [AddCommGroup A']

variable (B : Type uB) [AddCommGroup B]

theorem eq_zero_of_ofSpanSingleton_apply_self (a : A)
    (h : CharacterModule.ofSpanSingleton a ⟨a, Submodule.mem_span_singleton_self a⟩ = 0) : a = 0 := by
  erw [CharacterModule.ofSpanSingleton, LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply,
     CharacterModule.intSpanEquivQuotAddOrderOf_apply_self, Submodule.liftQSpanSingleton_apply,
    AddMonoidHom.coe_toIntLinearMap, int.divByNat, LinearMap.toSpanSingleton_apply_one,
    AddCircle.coe_eq_zero_iff] at h
  rcases h with ⟨n, hn⟩
  apply_fun Rat.den at hn
  rw [zsmul_one, Rat.den_intCast, Rat.inv_natCast_den_of_pos] at hn
  · split_ifs at hn
    · cases hn
    · rwa [eq_comm, AddMonoid.addOrderOf_eq_one_iff] at hn
  · grind

