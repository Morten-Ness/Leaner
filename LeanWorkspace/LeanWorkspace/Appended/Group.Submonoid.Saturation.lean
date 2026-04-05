import Mathlib

section

variable {M : Type*} [MulOneClass M]

theorem ext {s₁ s₂ : SaturatedSubmonoid M} (h : s₁.toSubmonoid = s₂.toSubmonoid) : s₁ = s₂ := SaturatedSubmonoid.toSubmonoid_injective h

end

section

variable {M : Type*}

variable [MulOneClass M]

theorem gc_saturation : GaloisConnection (Submonoid.saturation (M := M)) (·.toSubmonoid) := fun _ _ ↦
  ⟨fun ih _ hx ↦ ih <| SaturatedSubmonoid.mem_sInf.mpr fun _ ht ↦ ht hx,
  fun ih _ hx ↦ SaturatedSubmonoid.mem_sInf.mp hx _ ih⟩

end

section

variable {M : Type*}

variable [MulOneClass M]

theorem iSup_def {ι : Sort*} {f : ι → SaturatedSubmonoid M} :
    iSup f = (⨆ i, (f i).toSubmonoid).saturation := (Submonoid.giSaturation M).l_iSup_u f |>.symm

end

section

variable {M : Type*} [MulOneClass M] {s s₁ s₂ : Submonoid M}
  (h : s.MulSaturated) (h₁ : s₁.MulSaturated) (h₂ : s₂.MulSaturated)

include h₁ h₂ in
theorem inf : Submonoid.MulSaturated (s₁ ⊓ s₂) := fun _ _ hxy ↦ ⟨⟨(h₁ hxy.1).1, (h₂ hxy.2).1⟩, (h₁ hxy.1).2, (h₂ hxy.2).2⟩

end

section

variable {M : Type*}

variable [MulOneClass M]

variable {a : Submonoid M} {b : SaturatedSubmonoid M}

theorem le_toSubmonoid_saturation : a ≤ a.saturation.toSubmonoid := (Submonoid.gc_saturation M).le_u_l a

end

section

variable {M : Type*}

variable [CommMonoid M]

theorem mem_bot_iff {x : M} : x ∈ (⊥ : SaturatedSubmonoid M) ↔ IsUnit x := by
  simp_rw [SaturatedSubmonoid.bot_def, Submonoid.mem_saturation_iff, Submonoid.mem_bot, isUnit_iff_exists_inv]

end

section

variable {M : Type*}

variable [CommMonoid M]

variable {s : Submonoid M} {x : M}

theorem mem_saturation_iff' : x ∈ s.saturation ↔ ∃ y, y * x ∈ s := by
  simp_rw [Submonoid.mem_saturation_iff, mul_comm x]

end

section

variable {M : Type*}

variable [CommMonoid M]

variable {s : Submonoid M} {x : M}

theorem mem_saturation_iff : x ∈ s.saturation ↔ ∃ y, x * y ∈ s := by
  refine ⟨fun h ↦ ?_, fun ⟨y, hxy⟩ ↦ (s.saturation.2 <| Submonoid.le_toSubmonoid_saturation hxy).1⟩
  induction h using Submonoid.saturation_induction with
  | mem _ hx => exact ⟨1, by simpa⟩
  | mul _ _ _ _ ih₁ ih₂ =>
    exact ih₁.elim fun y₁ h₁ ↦ ih₂.elim fun y₂ h₂ ↦
      ⟨y₁ * y₂, by rw [mul_mul_mul_comm]; exact mul_mem h₁ h₂⟩
  | of_mul x₁ x₂ _ ih =>
    exact ih.elim fun y h ↦ ⟨⟨x₂ * y, by rwa [← mul_assoc]⟩,
      ⟨x₁ * y, by rwa [mul_left_comm, ← mul_assoc]⟩⟩

end

section

variable {M : Type*}

variable [CommMonoid M]

variable {s : Submonoid M} {x : M}

theorem mem_saturation_iff_exists_dvd : x ∈ s.saturation ↔ ∃ m ∈ s, x ∣ m := by
  simp_rw [dvd_def, existsAndEq, and_true, Submonoid.mem_saturation_iff]

end

section

variable {M : Type*} [MulOneClass M] {s s₁ s₂ : Submonoid M}
  (h : s.MulSaturated) (h₁ : s₁.MulSaturated) (h₂ : s₂.MulSaturated)

theorem of_left {M : Type*} [CommMonoid M] {s : Submonoid M}
    (h : ∀ ⦃x y⦄, x * y ∈ s → x ∈ s) : s.MulSaturated := fun x y hxy ↦ ⟨h hxy, h <| mul_comm x y ▸ hxy⟩

end

section

variable {M : Type*} [MulOneClass M] {s s₁ s₂ : Submonoid M}
  (h : s.MulSaturated) (h₁ : s₁.MulSaturated) (h₂ : s₂.MulSaturated)

theorem of_right {M : Type*} [CommMonoid M] {s : Submonoid M}
    (h : ∀ ⦃x y⦄, x * y ∈ s → y ∈ s) : s.MulSaturated := Submonoid.MulSaturated.of_left fun x y ↦ mul_comm x y ▸ @h y x

end

section

variable {M : Type*}

variable [MulOneClass M]

variable {a : Submonoid M} {b : SaturatedSubmonoid M}

theorem saturation_induction {s : Submonoid M}
    {p : (x : M) → x ∈ s.saturation → Prop}
    (mem : ∀ (x) (hx : x ∈ s), p x (Submonoid.le_toSubmonoid_saturation hx))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    (of_mul : ∀ (x y) (hxy : x * y ∈ s.saturation),
      p (x * y) hxy → p x (s.saturation.2 hxy).1 ∧ p y (s.saturation.2 hxy).2)
    {x : M} (hx : x ∈ s.saturation) : p x hx := by
  let s' : SaturatedSubmonoid M :=
  { carrier := { x | ∃ hx, p x hx }
    one_mem' := ⟨_ , mem 1 <| one_mem s⟩
    mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, mul _ _ _ _ hpx hpy⟩
    mulSaturated := fun x y ⟨_, hpxy⟩ ↦ ⟨⟨_, (of_mul _ _ _ hpxy).1⟩, ⟨_, (of_mul _ _ _ hpxy).2⟩⟩ }
  exact SaturatedSubmonoid.mem_sInf.mp hx s' (fun _ h ↦ ⟨_, mem _ h⟩) |>.2

end

section

variable {M : Type*} [MulOneClass M]

theorem saturation_sup {s₁ s₂ : Submonoid M} :
    (s₁ ⊔ s₂).saturation = s₁.saturation ⊔ s₂.saturation := (Submonoid.gc_saturation M).l_sup

-- note that it does not preserve Submonoid.MulSaturated.inf:
-- if s₁ = {6 ^ n | n : ℕ} and s₂ = {15 ^ n | n : ℕ} then
-- (s₁ ⊓ s₂).saturation = {1} and
-- s₁.saturation ⊓ s₂.saturation = {3 ^ n | n : ℕ}

end

section

variable {M : Type*}

variable [MulOneClass M]

variable {a : Submonoid M} {b : SaturatedSubmonoid M}

theorem saturation_toSubmonoid : b.saturation = b := (Submonoid.giSaturation M).l_u_eq b

end
