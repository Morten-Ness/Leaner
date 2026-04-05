import Mathlib

variable [GroupWithZero A] [GroupWithZero B] [MonoidWithZeroHomClass F A B] {f}

variable [MonoidWithZero A] [CommGroupWithZero B] [MonoidWithZeroHomClass F A B]

theorem mem_valueGroup_iff_of_comm {y : Bˣ} :
    y ∈ MonoidWithZeroHom.valueGroup f ↔ ∃ a, f a ≠ 0 ∧ ∃ x, f a * y = f x := by
  refine ⟨fun hy ↦ ?_, fun ⟨a, ha, x, hy⟩ ↦ ?_⟩
  · simp only [MonoidWithZeroHom.valueGroup, MonoidWithZeroHom.valueMonoid, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk] at hy
    induction hy using Subgroup.closure_induction with
    | mem _ h =>
      obtain ⟨a, ha⟩ := h
      exact ⟨a, ha.symm ▸ Units.ne_zero _, ⟨a * a, by simp [← ha]⟩⟩
    | one => exact ⟨1, by simp, 1, by simp⟩
    | mul c d hc hd hcy hdy =>
      obtain ⟨u, hu, a, ha⟩ := hcy
      obtain ⟨v, hv, b, hb⟩ := hdy
      refine ⟨u * v, by simp [hu, hv], a * b, ?_⟩
      simpa [map_mul, Units.val_mul, ← hb, ← ha] using mul_mul_mul_comm ..
    | inv c hc hcy =>
      obtain ⟨u, hu, a, ha⟩ := hcy
      exact ⟨a, by simp [← ha, hu], u, by simp [← ha]⟩
  · have hv : f x ≠ 0 := by
      simp only [← hy, ne_eq, mul_eq_zero, ha, Units.ne_zero, or_self, not_false_eq_true]
    let v := (Ne.isUnit hv).unit
    have hv₀ : f x = ↑v := IsUnit.unit_spec (Ne.isUnit hv)
    let u := (Ne.isUnit ha).unit
    have ha₀ : f a = ↑u := IsUnit.unit_spec (Ne.isUnit ha)
    rw_mod_cast [hv₀, ha₀, Eq.comm, ← inv_mul_eq_iff_eq_mul] at hy
    rw [← hy]
    apply Subgroup.mul_mem
    · apply MonoidWithZeroHom.inv_mem_valueGroup
      use a
    · apply MonoidWithZeroHom.mem_valueGroup
      use x

