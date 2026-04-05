import Mathlib

section

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem AffineMap.slope_comp {F PF : Type*} [AddCommGroup F] [Module k F] [AddTorsor F PF]
    (f : PE →ᵃ[k] PF) (g : k → PE) (a b : k) : slope (f ∘ g) a b = f.linear (slope g a b) := by
  simp only [slope, (· ∘ ·), f.linear.map_smul, f.linearMap_vsub]

end

section

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

variable [LinearOrder k] [IsStrictOrderedRing k] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono k E] {f : k → E} {x y : k}

theorem AntitoneOn.slope_nonpos {s : Set k} (hf : AntitoneOn f s) (hx : x ∈ s) (hy : y ∈ s) :
    slope f x y ≤ 0 := by
  simpa using hf.neg.slope_nonneg hx hy

end

section

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

variable [LinearOrder k] [IsStrictOrderedRing k] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono k E] {f : k → E} {x y : k}

theorem MonotoneOn.slope_nonneg {s : Set k} (hf : MonotoneOn f s) (hx : x ∈ s) (hy : y ∈ s) :
    0 ≤ slope f x y := by
  rcases le_total x y with hxy | hxy
  · exact (slope_nonneg_iff_of_le hxy).mpr (hf hx hy hxy)
  · exact slope_comm f x y ▸ (slope_nonneg_iff_of_le hxy).mpr (hf hy hx hxy)

end

section

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

variable [LinearOrder k] [IsStrictOrderedRing k] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono k E] {f : k → E} {x y : k}

theorem StrictAntiOn.slope_neg {s : Set k} (hf : StrictAntiOn f s) (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) : slope f x y < 0 := by
  simpa using hf.neg.slope_pos hx hy hxy

end

section

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

variable [LinearOrder k] [IsStrictOrderedRing k] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono k E] {f : k → E} {x y : k}

theorem StrictMonoOn.slope_pos {s : Set k} (hf : StrictMonoOn f s) (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) : 0 < slope f x y := by
  rcases lt_or_gt_of_ne hxy with hxy | hxy
  · exact (slope_pos_iff_of_le hxy.le).mpr (hf hx hy hxy)
  · exact slope_comm f x y ▸ (slope_pos_iff_of_le hxy.le).mpr (hf hy hx hxy)

end

section

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem eq_of_slope_eq_zero {f : k → PE} {a b : k} (h : slope f a b = (0 : E)) : f a = f b := by
  rw [← sub_smul_slope_vadd f a b, h, smul_zero, zero_vadd]

end

section

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem lineMap_slope_lineMap_slope_lineMap (f : k → PE) (a b r : k) :
    lineMap (slope f (lineMap a b r) b) (slope f a (lineMap a b r)) r = slope f a b := by
  obtain rfl | hab : a = b ∨ a ≠ b := Classical.em _; · simp
  rw [slope_comm _ a, slope_comm _ a, slope_comm _ _ b]
  convert lineMap_slope_slope_sub_div_sub f b (lineMap a b r) a hab.symm using 2
  rw [lineMap_apply_ring, eq_div_iff (sub_ne_zero.2 hab), sub_mul, one_mul, mul_sub, ← sub_sub,
    sub_sub_cancel]

end

section

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem lineMap_slope_slope_sub_div_sub (f : k → PE) (a b c : k) (h : a ≠ c) :
    lineMap (slope f a b) (slope f b c) ((c - b) / (c - a)) = slope f a c := by
  simp only [lineMap_apply_module, ← sub_div_sub_smul_slope_add_sub_div_sub_smul_slope f a b c,
    add_left_inj]
  match_scalars
  field [sub_ne_zero.2 h.symm]

end

section

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem slope_comm (f : k → PE) (a b : k) : slope f a b = slope f b a := by
  rw [slope, slope, ← neg_vsub_eq_vsub_rev, smul_neg, ← neg_smul, neg_inv, neg_sub]

end

section

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem slope_eq_zero_iff {f : k → E} {a b : k} : slope f a b = 0 ↔ f a = f b := by
  simp [slope, sub_eq_zero, eq_comm, or_iff_right_of_imp (congr_arg _)]

end

section

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

variable [LinearOrder k] [IsStrictOrderedRing k] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono k E] {f : k → E} {x y : k}

theorem slope_neg_iff_of_le (hxy : x ≤ y) : slope f x y < 0 ↔ f y < f x := by
  simpa using slope_pos_iff_of_le (f := -f) hxy

end

section

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

variable [LinearOrder k] [IsStrictOrderedRing k] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono k E] {f : k → E} {x y : k}

theorem slope_nonneg_iff_of_le (hxy : x ≤ y) : 0 ≤ slope f x y ↔ f x ≤ f y := by
  by_cases hxeqy : x = y
  · simp [hxeqy]
  refine ⟨fun h ↦ ?_, fun h ↦ smul_nonneg (inv_nonneg.2 (sub_nonneg.2 hxy)) ?_⟩
  · have := smul_nonneg (sub_nonneg.2 hxy) h
    rwa [slope, ← mul_smul, mul_inv_cancel₀ (mt sub_eq_zero.1 (Ne.symm hxeqy)), one_smul,
      vsub_eq_sub, sub_nonneg] at this
  · rwa [vsub_eq_sub, sub_nonneg]

end

section

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

variable [LinearOrder k] [IsStrictOrderedRing k] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono k E] {f : k → E} {x y : k}

theorem slope_nonpos_iff_of_le (hxy : x ≤ y) : slope f x y ≤ 0 ↔ f y ≤ f x := by
  simpa using slope_nonneg_iff_of_le (f := -f) hxy

end

section

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

variable [LinearOrder k] [IsStrictOrderedRing k] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono k E] {f : k → E} {x y : k}

theorem slope_pos_iff_of_le (hxy : x ≤ y) : 0 < slope f x y ↔ f x < f y := by
  simp_rw [lt_iff_le_and_ne, slope_nonneg_iff_of_le hxy, Ne, eq_comm, slope_eq_zero_iff]

end

section

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem slope_same (f : k → PE) (a : k) : (slope f a a : E) = 0 := by
  rw [slope, sub_self, inv_zero, zero_smul]

end

section

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem slope_sub_smul (f : k → E) {a b : k} (h : a ≠ b) :
    slope (fun x => (x - a) • f x) a b = f b := by
  simp [slope, inv_smul_smul₀ (sub_ne_zero.2 h.symm)]

end

section

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem slope_vadd_const (f : k → E) (c : PE) : (slope fun x => f x +ᵥ c) = slope f := by
  ext a b
  simp only [slope, vadd_vsub_vadd_cancel_right, vsub_eq_sub]

end

section

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

end

section

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem sub_smul_slope (f : k → PE) (a b : k) : (b - a) • slope f a b = f b -ᵥ f a := by
  rcases eq_or_ne a b with (rfl | hne)
  · rw [sub_self, zero_smul, vsub_self]
  · rw [slope, smul_inv_smul₀ (sub_ne_zero.2 hne.symm)]

end

section

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem sub_smul_slope_vadd (f : k → PE) (a b : k) : (b - a) • slope f a b +ᵥ f a = f b := by
  rw [sub_smul_slope, vsub_vadd]

end
