import Mathlib

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {a b : E} {r r' : k}

theorem left_le_lineMap_iff_le (h : 0 < r) : a ≤ lineMap a b r ↔ a ≤ b := Iff.trans (by rw [lineMap_apply_zero]) (lineMap_le_lineMap_iff_of_lt h)

end

section

variable {k E PE : Type*}

variable [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
  {a a' b b' : E} {r r' : k}

theorem left_le_lineMap_iff_nonneg (h : a < b) : a ≤ lineMap a b r ↔ 0 ≤ r := by
  rw [← lineMap_le_lineMap_iff_of_lt' h, lineMap_apply_zero]

end

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {a b : E} {r r' : k}

theorem left_le_midpoint : a ≤ midpoint k a b ↔ a ≤ b := left_le_lineMap_iff_le <| inv_pos.2 zero_lt_two

end

section

variable {k E PE : Type*}

variable [Ring k] [PartialOrder k] [IsOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]

variable {a a' b b' : E} {r r' : k}

variable [PosSMulReflectLT k E]

theorem left_lt_lineMap_iff_lt (h : 0 < r) : a < lineMap a b r ↔ a < b := Iff.trans (by rw [lineMap_apply_zero]) (lineMap_lt_lineMap_iff_of_lt h)

end

section

variable {k E PE : Type*}

variable [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
  {a a' b b' : E} {r r' : k}

theorem left_lt_lineMap_iff_pos (h : a < b) : a < lineMap a b r ↔ 0 < r := by
  rw [← lineMap_lt_lineMap_iff_of_lt' h, lineMap_apply_zero]

end

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {a b : E} {r r' : k}

theorem lineMap_le_left_iff_le (h : 0 < r) : lineMap a b r ≤ a ↔ b ≤ a := left_le_lineMap_iff_le (E := Eᵒᵈ) h

end

section

variable {k E PE : Type*}

variable [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
  {a a' b b' : E} {r r' : k}

theorem lineMap_le_left_iff_nonpos (h : a < b) : lineMap a b r ≤ a ↔ r ≤ 0 := by
  rw [← lineMap_le_lineMap_iff_of_lt' h, lineMap_apply_zero]

end

section

variable {k E PE : Type*}

variable [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
  {a a' b b' : E} {r r' : k}

theorem lineMap_le_lineMap_iff_of_lt' (h : a < b) : lineMap a b r ≤ lineMap a b r' ↔ r ≤ r' := by
  simp only [lineMap_apply_module']
  rw [add_le_add_iff_right, smul_le_smul_iff_of_pos_right (sub_pos.mpr h)]

end

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {a b : E} {r r' : k}

theorem lineMap_le_lineMap_iff_of_lt (h : r < r') : lineMap a b r ≤ lineMap a b r' ↔ a ≤ b := by
  simp only [lineMap_apply_module]
  rw [← le_sub_iff_add_le, add_sub_assoc, ← sub_le_iff_le_add', ← sub_smul, ← sub_smul,
    sub_sub_sub_cancel_left, smul_le_smul_iff_of_pos_left (sub_pos.2 h)]

end

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {f : k → E} {a b r : k}

theorem lineMap_le_map_iff_slope_le_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
    lineMap (f a) (f b) r ≤ f c ↔ slope f c b ≤ slope f a c := map_le_lineMap_iff_slope_le_slope (E := Eᵒᵈ) hab h₀ h₁

end

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {f : k → E} {a b r : k}

theorem lineMap_le_map_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
    lineMap (f a) (f b) r ≤ f c ↔ slope f a b ≤ slope f a c := map_le_lineMap_iff_slope_le_slope_left (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

end

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {f : k → E} {a b r : k}

theorem lineMap_le_map_iff_slope_le_slope_right (h : 0 < (1 - r) * (b - a)) :
    lineMap (f a) (f b) r ≤ f c ↔ slope f c b ≤ slope f a b := map_le_lineMap_iff_slope_le_slope_right (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

end

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {a b : E} {r r' : k}

theorem lineMap_le_right_iff_le (h : r < 1) : lineMap a b r ≤ b ↔ a ≤ b := Iff.trans (by rw [lineMap_apply_one]) (lineMap_le_lineMap_iff_of_lt h)

end

section

variable {k E PE : Type*}

variable [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
  {a a' b b' : E} {r r' : k}

theorem lineMap_le_right_iff_le_one (h : a < b) : lineMap a b r ≤ b ↔ r ≤ 1 := by
  rw [← lineMap_le_lineMap_iff_of_lt' h, lineMap_apply_one]

end

section

variable {k E PE : Type*}

variable [Ring k] [PartialOrder k] [IsOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]

variable {a a' b b' : E} {r r' : k}

variable [PosSMulReflectLT k E]

theorem lineMap_lt_left_iff_lt (h : 0 < r) : lineMap a b r < a ↔ b < a := left_lt_lineMap_iff_lt (E := Eᵒᵈ) h

end

section

variable {k E PE : Type*}

variable [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
  {a a' b b' : E} {r r' : k}

theorem lineMap_lt_left_iff_neg (h : a < b) : lineMap a b r < a ↔ r < 0 := by
  rw [← lineMap_lt_lineMap_iff_of_lt' h, lineMap_apply_zero]

end

section

variable {k E PE : Type*}

variable [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
  {a a' b b' : E} {r r' : k}

theorem lineMap_lt_lineMap_iff_of_lt' (h : a < b) : lineMap a b r < lineMap a b r' ↔ r < r' := by
  simp only [lineMap_apply_module']
  rw [add_lt_add_iff_right, smul_lt_smul_iff_of_pos_right (sub_pos.mpr h)]

end

section

variable {k E PE : Type*}

variable [Ring k] [PartialOrder k] [IsOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]

variable {a a' b b' : E} {r r' : k}

variable [PosSMulReflectLT k E]

theorem lineMap_lt_lineMap_iff_of_lt (h : r < r') : lineMap a b r < lineMap a b r' ↔ a < b := by
  simp only [lineMap_apply_module]
  rw [← lt_sub_iff_add_lt, add_sub_assoc, ← sub_lt_iff_lt_add', ← sub_smul, ← sub_smul,
    sub_sub_sub_cancel_left, smul_lt_smul_iff_of_pos_left (sub_pos.2 h)]

end

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {f : k → E} {a b r : k}

theorem lineMap_lt_map_iff_slope_lt_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
    lineMap (f a) (f b) r < f c ↔ slope f c b < slope f a c := map_lt_lineMap_iff_slope_lt_slope (E := Eᵒᵈ) hab h₀ h₁

end

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {f : k → E} {a b r : k}

theorem lineMap_lt_map_iff_slope_lt_slope_left (h : 0 < r * (b - a)) :
    lineMap (f a) (f b) r < f c ↔ slope f a b < slope f a c := map_lt_lineMap_iff_slope_lt_slope_left (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

end

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {f : k → E} {a b r : k}

theorem lineMap_lt_map_iff_slope_lt_slope_right (h : 0 < (1 - r) * (b - a)) :
    lineMap (f a) (f b) r < f c ↔ slope f c b < slope f a b := map_lt_lineMap_iff_slope_lt_slope_right (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

end

section

variable {k E PE : Type*}

variable [Ring k] [PartialOrder k] [IsOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]

variable {a a' b b' : E} {r r' : k}

variable [PosSMulReflectLT k E]

theorem lineMap_lt_right_iff_lt (h : r < 1) : lineMap a b r < b ↔ a < b := Iff.trans (by rw [lineMap_apply_one]) (lineMap_lt_lineMap_iff_of_lt h)

end

section

variable {k E PE : Type*}

variable [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
  {a a' b b' : E} {r r' : k}

theorem lineMap_lt_right_iff_lt_one (h : a < b) : lineMap a b r < b ↔ r < 1 := by
  rw [← lineMap_lt_lineMap_iff_of_lt' h, lineMap_apply_one]

end

section

variable {k E PE : Type*}

variable [Ring k] [PartialOrder k] [IsOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]

variable {a a' b b' : E} {r r' : k}

theorem lineMap_mono_endpoints (ha : a ≤ a') (hb : b ≤ b') (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
    lineMap a b r ≤ lineMap a' b' r := (lineMap_mono_left ha h₁).trans (lineMap_mono_right hb h₀)

end

section

variable {k E PE : Type*}

variable [Ring k] [PartialOrder k] [IsOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]

variable {a a' b b' : E} {r r' : k}

theorem lineMap_mono_left (ha : a ≤ a') (hr : r ≤ 1) : lineMap a b r ≤ lineMap a' b r := by
  simp only [lineMap_apply_module]
  gcongr
  exact sub_nonneg.2 hr

end

section

variable {k E PE : Type*}

variable [Ring k] [PartialOrder k] [IsOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]

variable {a a' b b' : E} {r r' : k}

theorem lineMap_mono_right (hb : b ≤ b') (hr : 0 ≤ r) : lineMap a b r ≤ lineMap a b' r := by
  simp only [lineMap_apply_module]
  gcongr

omit [IsOrderedRing k] in

end

section

variable {k E PE : Type*}

variable [Ring k] [PartialOrder k] [IsOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]

variable {a a' b b' : E} {r r' : k}

theorem lineMap_strict_mono_endpoints (ha : a < a') (hb : b < b') (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
    lineMap a b r < lineMap a' b' r := by
  rcases h₀.eq_or_lt with (rfl | h₀); · simpa
  exact (lineMap_mono_left ha.le h₁).trans_lt (lineMap_strict_mono_right hb h₀)

end

section

variable {k E PE : Type*}

variable [Ring k] [PartialOrder k] [IsOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]

variable {a a' b b' : E} {r r' : k}

theorem lineMap_strict_mono_left (ha : a < a') (hr : r < 1) : lineMap a b r < lineMap a' b r := by
  simp only [lineMap_apply_module]
  gcongr
  exact sub_pos.2 hr

omit [IsOrderedRing k] in

end

section

variable {k E PE : Type*}

variable [Ring k] [PartialOrder k] [IsOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]

variable {a a' b b' : E} {r r' : k}

theorem lineMap_strict_mono_right (hb : b < b') (hr : 0 < r) : lineMap a b r < lineMap a b' r := by
  simp only [lineMap_apply_module]; gcongr

end

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {f : k → E} {a b r : k}

theorem map_le_lineMap_iff_slope_le_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
    f c ≤ lineMap (f a) (f b) r ↔ slope f a c ≤ slope f c b := by
  rw [map_le_lineMap_iff_slope_le_slope_left (mul_pos h₀ (sub_pos.2 hab)), ←
    lineMap_slope_lineMap_slope_lineMap f a b r, right_le_lineMap_iff_le h₁]

end

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {f : k → E} {a b r : k}

theorem map_le_lineMap_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
    f c ≤ lineMap (f a) (f b) r ↔ slope f a c ≤ slope f a b := by
  rw [lineMap_apply, lineMap_apply, slope, slope, vsub_eq_sub, vsub_eq_sub, vsub_eq_sub,
    vadd_eq_add, vadd_eq_add, smul_eq_mul, add_sub_cancel_right, smul_sub, smul_sub, smul_sub,
    sub_le_iff_le_add, mul_inv_rev, mul_smul, mul_smul, ← smul_sub, ← smul_sub, ← smul_add,
    smul_smul, ← mul_inv_rev, inv_smul_le_iff_of_pos h, smul_smul,
    mul_inv_cancel_right₀ (right_ne_zero_of_mul h.ne'), smul_add,
    smul_inv_smul₀ (left_ne_zero_of_mul h.ne')]

end

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {f : k → E} {a b r : k}

theorem map_le_lineMap_iff_slope_le_slope_right (h : 0 < (1 - r) * (b - a)) :
    f c ≤ lineMap (f a) (f b) r ↔ slope f a b ≤ slope f c b := by
  rw [← lineMap_apply_one_sub, ← lineMap_apply_one_sub _ _ r]
  revert h; generalize 1 - r = r'; clear! r; intro h
  simp_rw [lineMap_apply, slope, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
  rw [sub_add_eq_sub_sub_swap, sub_self, zero_sub, neg_mul_eq_mul_neg, neg_sub,
    le_inv_smul_iff_of_pos h, smul_smul, mul_inv_cancel_right₀, le_sub_comm, ← neg_sub (f b),
    smul_neg, neg_add_eq_sub]
  · exact right_ne_zero_of_mul h.ne'

end

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {f : k → E} {a b r : k}

theorem map_lt_lineMap_iff_slope_lt_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
    f c < lineMap (f a) (f b) r ↔ slope f a c < slope f c b := lt_iff_lt_of_le_iff_le' (lineMap_le_map_iff_slope_le_slope hab h₀ h₁)
    (map_le_lineMap_iff_slope_le_slope hab h₀ h₁)

end

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {f : k → E} {a b r : k}

theorem map_lt_lineMap_iff_slope_lt_slope_left (h : 0 < r * (b - a)) :
    f c < lineMap (f a) (f b) r ↔ slope f a c < slope f a b := lt_iff_lt_of_le_iff_le' (lineMap_le_map_iff_slope_le_slope_left h)
    (map_le_lineMap_iff_slope_le_slope_left h)

end

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {f : k → E} {a b r : k}

theorem map_lt_lineMap_iff_slope_lt_slope_right (h : 0 < (1 - r) * (b - a)) :
    f c < lineMap (f a) (f b) r ↔ slope f a b < slope f c b := lt_iff_lt_of_le_iff_le' (lineMap_le_map_iff_slope_le_slope_right h)
    (map_le_lineMap_iff_slope_le_slope_right h)

end

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {a b : E} {r r' : k}

theorem midpoint_le_left : midpoint k a b ≤ a ↔ b ≤ a := lineMap_le_left_iff_le <| inv_pos.2 zero_lt_two

end

section

variable {k E PE : Type*}

variable [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
  {a a' b b' : E} {r r' : k}

theorem midpoint_le_midpoint [Invertible (2 : k)] (ha : a ≤ a') (hb : b ≤ b') :
    midpoint k a b ≤ midpoint k a' b' := lineMap_mono_endpoints ha hb (invOf_nonneg.2 zero_le_two) <| invOf_le_one one_le_two

end

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {a b : E} {r r' : k}

theorem midpoint_le_right : midpoint k a b ≤ b ↔ a ≤ b := lineMap_le_right_iff_le two_inv_lt_one

end

section

variable {k E PE : Type*}

theorem neg_of_slope_pos {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {f : 𝕜 → 𝕜} {x₀ b : 𝕜}
    (hb : b < x₀) (hbf : 0 < slope f x₀ b) (hf : f x₀ = 0) : f b < 0 := by
  rwa [slope_pos_iff_gt, hf] at hbf
  exact hb

end

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {a b : E} {r r' : k}

theorem right_le_lineMap_iff_le (h : r < 1) : b ≤ lineMap a b r ↔ b ≤ a := lineMap_le_right_iff_le (E := Eᵒᵈ) h

end

section

variable {k E PE : Type*}

variable [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
  {a a' b b' : E} {r r' : k}

theorem right_le_lineMap_iff_one_le (h : a < b) : b ≤ lineMap a b r ↔ 1 ≤ r := by
  rw [← lineMap_le_lineMap_iff_of_lt' h, lineMap_apply_one]

end

section

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {a b : E} {r r' : k}

theorem right_le_midpoint : b ≤ midpoint k a b ↔ b ≤ a := right_le_lineMap_iff_le two_inv_lt_one

end

section

variable {k E PE : Type*}

variable [Ring k] [PartialOrder k] [IsOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]

variable {a a' b b' : E} {r r' : k}

variable [PosSMulReflectLT k E]

theorem right_lt_lineMap_iff_lt (h : r < 1) : b < lineMap a b r ↔ b < a := lineMap_lt_right_iff_lt (E := Eᵒᵈ) h

end

section

variable {k E PE : Type*}

variable [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
  {a a' b b' : E} {r r' : k}

theorem right_lt_lineMap_iff_one_lt (h : a < b) : b < lineMap a b r ↔ 1 < r := by
  rw [← lineMap_lt_lineMap_iff_of_lt' h, lineMap_apply_one]

end

section

variable {k E PE : Type*}

theorem slope_pos_iff_gt {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {f : 𝕜 → 𝕜} {x₀ b : 𝕜} (hb : b < x₀) :
    0 < slope f x₀ b ↔ f b < f x₀ := by
  rw [slope_comm, slope_pos_iff hb]

end
