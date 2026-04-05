import Mathlib

section

variable {R : Type*} [NonUnitalSemiring R]

theorem add_inv_add_mul_eq_zero (u : (PreQuasiregular R)ˣ) :
    u.val.val + u⁻¹.val.val + u⁻¹.val.val * u.val.val = 0 := by
  simpa [-Units.inv_mul] using congr($(u.inv_mul).val)

end

section

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem iff_spectrum_nonneg {𝕜 A : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [Ring A] [PartialOrder A]
    [Algebra 𝕜 A] : NonnegSpectrumClass 𝕜 A ↔ ∀ a : A, 0 ≤ a → ∀ x ∈ spectrum 𝕜 a, 0 ≤ x := by
  simp [show NonnegSpectrumClass 𝕜 A ↔ _ from ⟨fun ⟨h⟩ ↦ h, (⟨·⟩)⟩,
    quasispectrum_eq_spectrum_union_zero]

alias ⟨_, of_spectrum_nonneg⟩ := iff_spectrum_nonneg

end

section

variable {R : Type*} [NonUnitalSemiring R]

theorem inv_add_add_mul_eq_zero (u : (PreQuasiregular R)ˣ) :
    u⁻¹.val.val + u.val.val + u.val.val * u⁻¹.val.val = 0 := by
  simpa [-Units.mul_inv] using congr($(u.mul_inv).val)

end

section

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem nonneg_of_mem_quasispectrum {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [PartialOrder A]
    [Module 𝕜 A] [NonnegSpectrumClass 𝕜 A] {a : A} (ha : 0 ≤ a) {x : 𝕜}
    (hx : x ∈ quasispectrum 𝕜 a) : 0 ≤ x := quasispectrum_nonneg_of_nonneg a ha x hx

grind_pattern nonneg_of_mem_quasispectrum => x ∈ quasispectrum 𝕜 a

end

section

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Module R A] [Module S A]

variable [Algebra R S] {a : A} {f : S → R}

theorem of_quasispectrum_eq {a b : A} {f : S → R} (ha : QuasispectrumRestricts a f)
    (h : quasispectrum S a = quasispectrum S b) : QuasispectrumRestricts b f where
  rightInvOn := h ▸ ha.rightInvOn
  left_inv := ha.left_inv

end

section

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem quasispectrum_inr_eq (R S : Type*) {A : Type*} [Semifield R]
    [Field S] [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] (a : A) :
    quasispectrum R (a : Unitization S A) = quasispectrum R a := by
  rw [quasispectrum_eq_spectrum_union_zero, Unitization.quasispectrum_eq_spectrum_inr' R S]
  simpa using Unitization.zero_mem_spectrum_inr _ _ _

end

section

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable {R S A : Type*} [Semifield R] [Semifield S] [Ring A]

variable [Algebra R S] [Algebra R A] [Algebra S A] {a : A} {f : S → R}

theorem rightInvOn (h : SpectrumRestricts a f) : (spectrum S a).RightInvOn f (algebraMap R S) := (QuasispectrumRestricts.rightInvOn h).mono <| spectrum_subset_quasispectrum _ _

end

section

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

theorem unitsFstOne_val_inv_val_fst (x : (Unitization.unitsFstOne R A)) : x.val⁻¹.val.fst = 1 := Unitization.mem_unitsFstOne.mp x⁻¹.property

end

section

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

theorem unitsFstOne_val_val_fst (x : (Unitization.unitsFstOne R A)) : x.val.val.fst = 1 := Unitization.mem_unitsFstOne.mp x.property

end

section

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem zero_mem_spectrum_inr (R S : Type*) {A : Type*} [CommSemiring R]
    [CommRing S] [Nontrivial S] [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] (a : A) :
    0 ∈ spectrum R (a : Unitization S A) := by
  rw [spectrum.zero_mem_iff]
  rintro ⟨u, hu⟩
  simpa [-Units.mul_inv, hu] using congr($(u.mul_inv).fst)

end
