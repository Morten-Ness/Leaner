import Mathlib

section

theorem Irreducible.coe_ne_zero {M₀ S : Type*} [MonoidWithZero M₀] [SetLike S M₀]
    [SubmonoidClass S M₀] {s : S} {x : s} (hx : Irreducible x) : (x : M₀) ≠ 0 := fun h ↦ hx.1 <| by simpa using hx.2 (a := x) (b := x) (by ext; simp [h])

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem IsLeftRegular.mem_nonZeroDivisorsLeft (h : IsLeftRegular r) :
    r ∈ nonZeroDivisorsLeft M₀ := fun _x hx ↦ h.mul_left_eq_zero_iff.mp hx

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem IsRegular.mem_nonZeroDivisors (h : IsRegular r) : r ∈ M₀⁰ := ⟨h.1.mem_nonZeroDivisorsLeft, h.2.mem_nonZeroDivisorsRight⟩

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem IsRightRegular.mem_nonZeroDivisorsRight (h : IsRightRegular r) :
    r ∈ nonZeroDivisorsRight M₀ := fun _x hx ↦ h.mul_right_eq_zero_iff.mp hx

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem IsUnit.mem_nonZeroDivisors (hx : IsUnit x) : x ∈ M₀⁰ := ⟨fun _ ↦ hx.mul_right_eq_zero.mp, fun _ ↦ hx.mul_left_eq_zero.mp⟩

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [FunLike F M₀ M₀']

theorem MulEquivClass.map_nonZeroDivisors {M₀ S F : Type*} [MonoidWithZero M₀] [MonoidWithZero S]
    [EquivLike F M₀ S] [MulEquivClass F M₀ S] (h : F) :
    Submonoid.map h (nonZeroDivisors M₀) = nonZeroDivisors S := by
  let h : M₀ ≃* S := h
  change Submonoid.map h _ = _
  ext
  simp_rw [Submonoid.map_equiv_eq_comap_symm, Submonoid.mem_comap, mem_nonZeroDivisors_iff,
    ← h.symm.forall_congr_right, h.symm.toEquiv_eq_coe, h.symm.coe_toEquiv, ← map_mul,
    map_eq_zero_iff _ h.symm.injective]

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [FunLike F M₀ M₀']

theorem comap_nonZeroDivisors_le_of_injective [MonoidWithZeroHomClass F M₀ M₀'] {f : F}
    (hf : Function.Injective f) : M₀'⁰.comap f ≤ M₀⁰ := fun _ ha ↦ mem_nonZeroDivisors_of_injective hf (Submonoid.mem_comap.mp ha)

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [NoZeroDivisors M₀]

theorem eq_zero_of_ne_zero_of_mul_left_eq_zero (hx : x ≠ 0) (hxy : x * y = 0) : y = 0 := Or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hx

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [NoZeroDivisors M₀]

theorem eq_zero_of_ne_zero_of_mul_right_eq_zero (hx : x ≠ 0) (hxy : y * x = 0) : y = 0 := Or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hx

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem isSMulRegular_iff_mem_nonZeroSMulDivisors {M : Type*} [AddGroup M] [DistribMulAction M₀ M]
    {m₀ : M₀} : IsSMulRegular M m₀ ↔ m₀ ∈ nonZeroSMulDivisors M₀ M := isSMulRegular_iff_right_eq_zero_of_smul

end

section

variable {G₀ : Type*} [GroupWithZero G₀] {x : G₀}

theorem isUnit_of_mem_nonZeroDivisors (hx : x ∈ nonZeroDivisors G₀) : IsUnit x := (nonZeroDivisorsEquivUnits ⟨x, hx⟩).isUnit

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [NoZeroDivisors M₀]

theorem le_nonZeroDivisors_of_noZeroDivisors {S : Submonoid M₀} (hS : (0 : M₀) ∉ S) :
    S ≤ M₀⁰ := fun _ hx ↦
  mem_nonZeroDivisors_of_ne_zero <| by rintro rfl; exact hS hx

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [FunLike F M₀ M₀']

theorem map_le_nonZeroDivisors_of_injective [NoZeroDivisors M₀'] [MonoidWithZeroHomClass F M₀ M₀']
    (f : F) (hf : Function.Injective f) {S : Submonoid M₀} (hS : S ≤ M₀⁰) : S.map f ≤ M₀'⁰ := by
  cases subsingleton_or_nontrivial M₀
  · simp [Subsingleton.elim S ⊥]
  · refine le_nonZeroDivisors_of_noZeroDivisors ?_
    rintro ⟨x, hx, hx0⟩
    exact zero_notMem_nonZeroDivisors <| hS <| map_eq_zero_iff f hf |>.mp hx0 ▸ hx

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [FunLike F M₀ M₀']

theorem map_mem_nonZeroDivisors [Nontrivial M₀] [NoZeroDivisors M₀'] [ZeroHomClass F M₀ M₀'] (g : F)
    (hg : Function.Injective g) {x : M₀} (h : x ∈ M₀⁰) : g x ∈ M₀'⁰ := ⟨fun _ ↦ eq_zero_of_ne_zero_of_mul_left_eq_zero (map_ne_zero_of_mem_nonZeroDivisors g hg h),
    fun _ ↦ eq_zero_of_ne_zero_of_mul_right_eq_zero (map_ne_zero_of_mem_nonZeroDivisors g hg h)⟩

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [FunLike F M₀ M₀']

theorem map_ne_zero_of_mem_nonZeroDivisors [Nontrivial M₀] [ZeroHomClass F M₀ M₀'] (g : F)
    (hg : Function.Injective (g : M₀ → M₀')) {x : M₀} (h : x ∈ M₀⁰) : g x ≠ 0 := fun h0 ↦
  one_ne_zero (h.2 1 ((one_mul x).symm ▸ hg (h0.trans (map_zero g).symm)))

end

section

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem mem_nonZeroDivisors_iff_left : r ∈ M₀⁰ ↔ ∀ x, r * x = 0 → x = 0 := by
  rw [← nonZeroDivisorsLeft_eq_nonZeroDivisors]; rfl

end

section

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem mem_nonZeroDivisors_iff_right : r ∈ M₀⁰ ↔ ∀ x, x * r = 0 → x = 0 := by
  rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]; rfl

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [FunLike F M₀ M₀']

theorem mem_nonZeroDivisors_of_injective [MonoidWithZeroHomClass F M₀ M₀'] {f : F}
    (hf : Function.Injective f) (hx : f x ∈ M₀'⁰) : x ∈ M₀⁰ := ⟨fun y hy ↦ hf <| map_zero f ▸ hx.1 (f y) (map_mul f x y ▸ map_zero f ▸ congrArg f hy),
    fun y hy ↦ hf <| map_zero f ▸ hx.2 (f y) (map_mul f y x ▸ map_zero f ▸ congrArg f hy)⟩

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [NoZeroDivisors M₀]

theorem mem_nonZeroDivisors_of_ne_zero (hx : x ≠ 0) : x ∈ M₀⁰ := ⟨fun _ ↦ eq_zero_of_ne_zero_of_mul_left_eq_zero hx,
   fun _ ↦ eq_zero_of_ne_zero_of_mul_right_eq_zero hx⟩

end

section

open scoped nonZeroDivisors

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a : M₀}

theorem mk_mem_nonZeroDivisors_associates : Associates.mk a ∈ (Associates M₀)⁰ ↔ a ∈ M₀⁰ := by
  rw [mem_nonZeroDivisors_iff_right, mem_nonZeroDivisors_iff_right]
  contrapose!
  constructor
  · rintro ⟨⟨x⟩, hx₁, hx₂⟩
    refine ⟨x, ?_, ?_⟩
    · rwa [← Associates.mk_eq_zero, ← Associates.mk_mul_mk, ← Associates.quot_mk_eq_mk]
    · rwa [← Associates.mk_ne_zero, ← Associates.quot_mk_eq_mk]
  · refine fun ⟨b, hb₁, hb₂⟩ ↦ ⟨Associates.mk b, ?_, by rwa [Associates.mk_ne_zero]⟩
    rw [Associates.mk_mul_mk, hb₁, Associates.mk_zero]

end

section

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem mul_left_coe_nonZeroDivisors_eq_zero_iff {c : M₀⁰} : (c : M₀) * x = 0 ↔ x = 0 := mul_left_mem_nonZeroDivisors_eq_zero_iff c.prop

end

section

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem mul_left_mem_nonZeroDivisors_eq_zero_iff (hr : r ∈ M₀⁰) : r * x = 0 ↔ x = 0 := by
  rw [mul_comm, mul_right_mem_nonZeroDivisors_eq_zero_iff hr]

end

section

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem mul_mem_nonZeroDivisors : a * b ∈ M₀⁰ ↔ a ∈ M₀⁰ ∧ b ∈ M₀⁰ where
  mp h := by
    rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]
    constructor <;> intro x h' <;> apply h.2
    · rw [← mul_assoc, h', zero_mul]
    · rw [mul_comm a b, ← mul_assoc, h', zero_mul]
  mpr := fun h ↦ mul_mem h.1 h.2

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem mul_mem_nonZeroDivisors_of_mem_nonZeroDivisors (hx : x ∈ M₀⁰) (hy : y ∈ M₀⁰) :
    x * y ∈ M₀⁰ := mem_nonZeroDivisors_iff'.mpr ⟨Submonoid.mul_mem _ hx.1 hy.1, Submonoid.mul_mem _ hx.2 hy.2⟩

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem mul_right_coe_nonZeroDivisors_eq_zero_iff {c : M₀⁰} : x * c = 0 ↔ x = 0 := mul_right_mem_nonZeroDivisors_eq_zero_iff c.prop

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem mul_right_mem_nonZeroDivisors_eq_zero_iff (hr : r ∈ M₀⁰) : x * r = 0 ↔ x = 0 := mul_right_mem_nonZeroDivisorsRight_eq_zero_iff hr.2

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem noZeroDivisors_iff_forall_mem_nonZeroDivisorsLeft :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → x ∈ nonZeroDivisorsLeft M₀ := noZeroDivisors_iff_right_eq_zero_of_mul

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem noZeroDivisors_iff_forall_mem_nonZeroDivisorsRight :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → x ∈ nonZeroDivisorsRight M₀ := noZeroDivisors_iff_left_eq_zero_of_mul

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [Nontrivial M₀]

theorem nonZeroDivisors.ne_zero (hx : x ∈ M₀⁰) : x ≠ 0 := ne_of_mem_of_not_mem hx zero_notMem_nonZeroDivisors

end

section

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem nonZeroDivisorsLeft_eq_nonZeroDivisors : nonZeroDivisorsLeft M₀ = nonZeroDivisors M₀ := by
  rw [nonZeroDivisors, nonZeroDivisorsLeft_eq_right, inf_idem]

end

section

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem nonZeroDivisorsRight_eq_left : nonZeroDivisorsRight M₀ = nonZeroDivisorsLeft M₀ := by
  rw [nonZeroDivisorsLeft_eq_right]

end

section

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem nonZeroDivisorsRight_eq_nonZeroDivisors : nonZeroDivisorsRight M₀ = nonZeroDivisors M₀ := by
  rw [← nonZeroDivisorsLeft_eq_right, nonZeroDivisorsLeft_eq_nonZeroDivisors]

end

section

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem nonZeroDivisors_dvd_iff_dvd_coe {a b : M₀⁰} :
    a ∣ b ↔ (a : M₀) ∣ (b : M₀) := ⟨fun ⟨c, hc⟩ ↦ by simp_rw [hc, Submonoid.coe_mul, dvd_mul_right],
  fun ⟨c, hc⟩ ↦ ⟨⟨c, (mul_mem_nonZeroDivisors.mp (hc ▸ b.prop)).2⟩,
    by simp_rw [Subtype.ext_iff, Submonoid.coe_mul, hc]⟩⟩

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [FunLike F M₀ M₀']

theorem nonZeroDivisors_le_comap_nonZeroDivisors_of_injective [NoZeroDivisors M₀']
    [MonoidWithZeroHomClass F M₀ M₀'] (f : F) (hf : Function.Injective f) : M₀⁰ ≤ M₀'⁰.comap f := Submonoid.le_comap_of_map_le _ (map_le_nonZeroDivisors_of_injective _ hf le_rfl)

end

section

variable (M₀ : Type*) [MonoidWithZero M₀] {x : M₀}

theorem notMem_nonZeroDivisorsLeft_iff :
    x ∉ nonZeroDivisorsLeft M₀ ↔ {y | x * y = 0 ∧ y ≠ 0}.Nonempty := by
  simpa [mem_nonZeroDivisorsLeft_iff] using Set.nonempty_def.symm

end

section

variable (M₀ : Type*) [MonoidWithZero M₀] {x : M₀}

theorem notMem_nonZeroDivisorsRight_iff :
    x ∉ nonZeroDivisorsRight M₀ ↔ {y | y * x = 0 ∧ y ≠ 0}.Nonempty := by
  simpa [mem_nonZeroDivisorsRight_iff] using Set.nonempty_def.symm

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem notMem_nonZeroDivisors_iff :
    r ∉ M₀⁰ ↔ {s | r * s = 0 ∧ s ≠ 0}.Nonempty ∨ {s | s * r = 0 ∧ s ≠ 0}.Nonempty := by
  simp [-not_and, not_and_or, mem_nonZeroDivisors_iff, Set.nonempty_def]

end

section

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem notMem_nonZeroDivisors_iff_left : r ∉ M₀⁰ ↔ {s | r * s = 0 ∧ s ≠ 0}.Nonempty := by
  simp [mem_nonZeroDivisors_iff_left, Set.nonempty_def]

end

section

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem notMem_nonZeroDivisors_iff_right : r ∉ M₀⁰ ↔ {s | s * r = 0 ∧ s ≠ 0}.Nonempty := by
  simp [mem_nonZeroDivisors_iff_right, Set.nonempty_def]

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [NoZeroDivisors M₀]

theorem powers_le_nonZeroDivisors_of_noZeroDivisors (hx : x ≠ 0) : Submonoid.powers x ≤ M₀⁰ := le_nonZeroDivisors_of_noZeroDivisors fun h ↦ hx (h.recOn fun _ ↦ eq_zero_of_pow_eq_zero)

end

section

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem prod_mem_nonZeroDivisors_of_mem_nonZeroDivisors
    {ι : Type*} {s : Finset ι} {f : ι → M₀} (h : ∀ i ∈ s, f i ∈ M₀⁰) :
    ∏ i ∈ s, f i ∈ M₀⁰ := s.prod_induction _ _ (fun _ _ ↦ and_imp.mp mul_mem_nonZeroDivisors.mpr) (one_mem _) h

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [Nontrivial M₀]

theorem zero_notMem_nonZeroDivisors : 0 ∉ M₀⁰ := fun h ↦ zero_notMem_nonZeroDivisorsLeft h.1

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [Nontrivial M₀]

theorem zero_notMem_nonZeroDivisorsLeft : 0 ∉ nonZeroDivisorsLeft M₀ := fun h ↦ one_ne_zero <| h 1 <| zero_mul _

end

section

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [Nontrivial M₀]

theorem zero_notMem_nonZeroDivisorsRight : 0 ∉ nonZeroDivisorsRight M₀ := fun h ↦ one_ne_zero <| h 1 <| mul_zero _

end
