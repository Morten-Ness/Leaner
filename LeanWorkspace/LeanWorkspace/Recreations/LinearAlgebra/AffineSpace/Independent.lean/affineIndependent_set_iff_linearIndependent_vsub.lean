import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

theorem affineIndependent_set_iff_linearIndependent_vsub {s : Set P} {p₁ : P} (hp₁ : p₁ ∈ s) :
    AffineIndependent k (fun p => p : s → P) ↔
      LinearIndependent k (fun v => v : (fun p => (p -ᵥ p₁ : V)) '' (s \ {p₁}) → V) := by
  rw [affineIndependent_iff_linearIndependent_vsub k (fun p => p : s → P) ⟨p₁, hp₁⟩]
  constructor
  · intro h
    have hv : ∀ v : (fun p => (p -ᵥ p₁ : V)) '' (s \ {p₁}), (v : V) +ᵥ p₁ ∈ s \ {p₁} := fun v =>
      (vsub_left_injective p₁).mem_set_image.1 ((vadd_vsub (v : V) p₁).symm ▸ v.property)
    let f : (fun p : P => (p -ᵥ p₁ : V)) '' (s \ {p₁}) → { x : s // x ≠ ⟨p₁, hp₁⟩ } := fun x =>
      ⟨⟨(x : V) +ᵥ p₁, Set.mem_of_mem_diff (hv x)⟩, fun hx =>
        Set.notMem_of_mem_diff (hv x) (Subtype.ext_iff.1 hx)⟩
    convert h.comp f fun x1 x2 hx =>
        Subtype.ext (vadd_right_cancel p₁ (Subtype.ext_iff.1 (Subtype.ext_iff.1 hx)))
    ext v
    exact (vadd_vsub (v : V) p₁).symm
  · intro h
    let f : { x : s // x ≠ ⟨p₁, hp₁⟩ } → (fun p : P => (p -ᵥ p₁ : V)) '' (s \ {p₁}) := fun x =>
      ⟨((x : s) : P) -ᵥ p₁, ⟨x, ⟨⟨(x : s).property, fun hx => x.property (Subtype.ext hx)⟩, rfl⟩⟩⟩
    convert h.comp f fun x1 x2 hx =>
        Subtype.ext (Subtype.ext (vsub_left_cancel (Subtype.ext_iff.1 hx)))

