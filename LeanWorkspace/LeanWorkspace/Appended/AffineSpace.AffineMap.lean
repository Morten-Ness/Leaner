import Mathlib

section

variable {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*} {V3 : Type*}
  {P3 : Type*} {V4 : Type*} {P4 : Type*} [Ring k] [AddCommGroup V1] [Module k V1]
  [AddTorsor V1 P1] [AddCommGroup V2] [Module k V2] [AddTorsor V2 P2] [AddCommGroup V3]
  [Module k V3] [AddTorsor V3 P3] [AddCommGroup V4] [Module k V4] [AddTorsor V4 P4]

theorem apply_lineMap (f : P1 →ᵃ[k] P2) (p₀ p₁ : P1) (c : k) :
    f (AffineMap.lineMap p₀ p₁ c) = AffineMap.lineMap (f p₀) (f p₁) c := by
  simp [AffineMap.lineMap_apply]

end

section

variable {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*} {V3 : Type*}
  {P3 : Type*} {V4 : Type*} {P4 : Type*} [Ring k] [AddCommGroup V1] [Module k V1]
  [AddTorsor V1 P1] [AddCommGroup V2] [Module k V2] [AddTorsor V2 P2] [AddCommGroup V3]
  [Module k V3] [AddTorsor V3 P3] [AddCommGroup V4] [Module k V4] [AddTorsor V4 P4]

theorem ext_linear_iff {f g : P1 →ᵃ[k] P2} : f = g ↔ (f.linear = g.linear) ∧ (∃ p, f p = g p) := ⟨fun h ↦ ⟨congrArg _ h, by inhabit P1; exact default, by rw [h]⟩,
  fun h ↦ Exists.casesOn h.2 fun _ hp ↦ AffineMap.ext_linear h.1 hp⟩

end

section

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [CommRing k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2]

variable [Module k V1] [Module k V2]

theorem homothety_eq_iff_of_mul_eq_one {c p q : P1} {r₁ r₂ : k} (h : r₁ * r₂ = 1) :
    AffineMap.homothety c r₁ p = q ↔ AffineMap.homothety c r₂ q = p := by
  obtain h' : r₂ * r₁ = 1 := mul_eq_one_comm.mp h
  refine ⟨fun h1 ↦ ?_, fun h1 ↦ ?_⟩
  all_goals
    rw [← h1, ← AffineMap.homothety_mul_apply]
    simp [h, h']

end

section

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [CommRing k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2]

variable [Module k V1] [Module k V2]

theorem homothety_inj [Module.IsTorsionFree k V1] [IsCancelMulZero k] (c : P1) {r : k} (hr : r ≠ 0)
    {p q : P1} :
    AffineMap.homothety c r p = AffineMap.homothety c r q ↔ p = q := (AffineMap.homothety_injective c hr).eq_iff

end

section

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [CommRing k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2]

variable [Module k V1] [Module k V2]

theorem homothety_injective [Module.IsTorsionFree k V1] [IsCancelMulZero k] (c : P1) {r : k}
    (hr : r ≠ 0) :
    Function.Injective (AffineMap.homothety c r) := fun _ _ h ↦ by simpa [AffineMap.homothety_def, hr] using h

end

section

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [CommRing k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2]

variable [Module k V1] [Module k V2]

theorem homothety_mul (c : P1) (r₁ r₂ : k) :
    AffineMap.homothety c (r₁ * r₂) = (AffineMap.homothety c r₁).comp (AffineMap.homothety c r₂) := AffineMap.ext <| AffineMap.homothety_mul_apply c r₁ r₂

end

section

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [CommRing k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2]

variable [Module k V1] [Module k V2]

theorem homothety_mul_apply (c : P1) (r₁ r₂ : k) (p : P1) :
    AffineMap.homothety c (r₁ * r₂) p = AffineMap.homothety c r₁ (AffineMap.homothety c r₂ p) := by
  simp only [AffineMap.homothety_apply, mul_smul, vadd_vsub]

end

section

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [CommRing k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2]

variable [Module k V1] [Module k V2]

theorem homothety_zero (c : P1) : AffineMap.homothety c (0 : k) = AffineMap.const k P1 c := by
  ext p
  simp [AffineMap.homothety_apply]

end

section

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [Ring k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2] [AddTorsor V2 P2]

variable [AddCommGroup V3] [AddTorsor V3 P3] [Module k V1] [Module k V2] [Module k V3]

theorem lineMap_apply' [SMulCommClass k k V2] (f g : P1 →ᵃ[k] P2) (c : k)
    (p : P1) : AffineMap.lineMap f g c p = AffineMap.lineMap (f p) (g p) c := by
  simp [AffineMap.lineMap_apply]

end

section

variable {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*} {V3 : Type*}
  {P3 : Type*} {V4 : Type*} {P4 : Type*} [Ring k] [AddCommGroup V1] [Module k V1]
  [AddTorsor V1 P1] [AddCommGroup V2] [Module k V2] [AddTorsor V2 P2] [AddCommGroup V3]
  [Module k V3] [AddTorsor V3 P3] [AddCommGroup V4] [Module k V4] [AddTorsor V4 P4]

theorem linearMap_vsub (f : P1 →ᵃ[k] P2) (p1 p2 : P1) : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2 := by
  conv_rhs => rw [← vsub_vadd p1 p2, AffineMap.map_vadd, vadd_vsub]

end

section

variable {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*} {V3 : Type*}
  {P3 : Type*} {V4 : Type*} {P4 : Type*} [Ring k] [AddCommGroup V1] [Module k V1]
  [AddTorsor V1 P1] [AddCommGroup V2] [Module k V2] [AddTorsor V2 P2] [AddCommGroup V3]
  [Module k V3] [AddTorsor V3 P3] [AddCommGroup V4] [Module k V4] [AddTorsor V4 P4]

variable (k P1)

variable {k P1}

theorem linear_eq_zero_iff_exists_const (f : P1 →ᵃ[k] P2) :
    f.linear = 0 ↔ ∃ q, f = AffineMap.const k P1 q := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · use f (Classical.arbitrary P1)
    ext
    rw [AffineMap.coe_const, Function.const_apply, ← @vsub_eq_zero_iff_eq V2, ← AffineMap.linearMap_vsub f, h,
      LinearMap.zero_apply]
  · rcases h with ⟨q, rfl⟩
    exact AffineMap.const_linear k P1 q

end

section

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [Ring k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2] [AddTorsor V2 P2]

variable [AddCommGroup V3] [AddTorsor V3 P3] [Module k V1] [Module k V2] [Module k V3]

variable {ι : Type*} {φv φp : ι → Type*} [(i : ι) → AddCommGroup (φv i)]
  [(i : ι) → Module k (φv i)] [(i : ι) → AddTorsor (φv i) (φp i)]

variable (fp : (i : ι) → (P1 →ᵃ[k] φp i)) (fv : (i : ι) → (P1 →ᵃ[k] φv i))
  (f' : ι → P1 →ᵃ[k] P2)

theorem pi_eq_zero : AffineMap.pi fv = 0 ↔ ∀ i, fv i = 0 := by
  simp only [AffineMap.ext_iff, funext_iff, AffineMap.pi_apply]
  exact forall_comm

end

section

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [Ring k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2] [AddTorsor V2 P2]

variable [AddCommGroup V3] [AddTorsor V3 P3] [Module k V1] [Module k V2] [Module k V3]

variable {ι : Type*} {φv φp : ι → Type*} [(i : ι) → AddCommGroup (φv i)]
  [(i : ι) → Module k (φv i)] [(i : ι) → AddTorsor (φv i) (φp i)]

variable (fp : (i : ι) → (P1 →ᵃ[k] φp i)) (fv : (i : ι) → (P1 →ᵃ[k] φv i))
  (f' : ι → P1 →ᵃ[k] P2)

variable [Finite ι] [DecidableEq ι] {f g : ((i : ι) → φv i) →ᵃ[k] P2}

theorem pi_ext_nonempty' [Nonempty ι] (h : ∀ i, f.comp (LinearMap.single _ _ i).toAffineMap =
    g.comp (LinearMap.single _ _ i).toAffineMap) : f = g := by
  refine AffineMap.pi_ext_nonempty fun i x => ?_
  convert AffineMap.congr_fun (h i) x

end

section

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [Ring k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2] [AddTorsor V2 P2]

variable [AddCommGroup V3] [AddTorsor V3 P3] [Module k V1] [Module k V2] [Module k V3]

variable {ι : Type*} {φv φp : ι → Type*} [(i : ι) → AddCommGroup (φv i)]
  [(i : ι) → Module k (φv i)] [(i : ι) → AddTorsor (φv i) (φp i)]

variable (fp : (i : ι) → (P1 →ᵃ[k] φp i)) (fv : (i : ι) → (P1 →ᵃ[k] φv i))
  (f' : ι → P1 →ᵃ[k] P2)

variable [Finite ι] [DecidableEq ι] {f g : ((i : ι) → φv i) →ᵃ[k] P2}

theorem pi_ext_nonempty [Nonempty ι] (h : ∀ i x, f (Pi.single i x) = g (Pi.single i x)) :
    f = g := by
  apply AffineMap.pi_ext_zero h
  inhabit ι
  rw [← Pi.single_zero default]
  apply h

end

section

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [Ring k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2] [AddTorsor V2 P2]

variable [AddCommGroup V3] [AddTorsor V3 P3] [Module k V1] [Module k V2] [Module k V3]

variable {ι : Type*} {φv φp : ι → Type*} [(i : ι) → AddCommGroup (φv i)]
  [(i : ι) → Module k (φv i)] [(i : ι) → AddTorsor (φv i) (φp i)]

variable (fp : (i : ι) → (P1 →ᵃ[k] φp i)) (fv : (i : ι) → (P1 →ᵃ[k] φv i))
  (f' : ι → P1 →ᵃ[k] P2)

variable [Finite ι] [DecidableEq ι] {f g : ((i : ι) → φv i) →ᵃ[k] P2}

theorem pi_ext_zero (h : ∀ i x, f (Pi.single i x) = g (Pi.single i x)) (h₂ : f 0 = g 0) :
    f = g := by
  apply AffineMap.ext_linear
  · apply LinearMap.pi_ext
    intro i x
    have s₁ := h i x
    have s₂ := AffineMap.map_vadd f 0 (Pi.single i x)
    have s₃ := AffineMap.map_vadd g 0 (Pi.single i x)
    rw [vadd_eq_add, add_zero] at s₂ s₃
    replace h₂ := h i 0
    simp only [Pi.single_zero] at h₂
    rwa [s₂, s₃, h₂, vadd_right_cancel_iff] at s₁
  · exact h₂

end
