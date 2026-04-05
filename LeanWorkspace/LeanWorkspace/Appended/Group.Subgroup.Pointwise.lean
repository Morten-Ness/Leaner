import Mathlib

section

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem smul_mem_of_mem_closure_of_mem {X : Type*} [MulAction G X] {s : Set G} {t : Set X}
    (hs : ∀ g ∈ s, g⁻¹ ∈ s) (hst : ∀ᵉ (g ∈ s) (x ∈ t), g • x ∈ t) {g : G}
    (hg : g ∈ Subgroup.closure s) {x : X} (hx : x ∈ t) : g • x ∈ t := by
  induction hg using Subgroup.closure_induction'' generalizing x with
  | one => simpa
  | mem g' hg' => exact hst g' hg' x hx
  | inv_mem g' hg' => exact hst g'⁻¹ (hs g' hg') x hx
  | mul _ _ _ _ h₁ h₂ => rw [mul_smul]; exact h₁ (h₂ hx)

end

section

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem smul_opposite_image_mul_preimage {H : Subgroup G} (g : G) (h : H.op) (s : Set G) :
    (fun y => h • y) '' ((g * ·) ⁻¹' s) = (g * ·) ⁻¹' ((fun y => h • y) '' s) := Subgroup.smul_opposite_image_mul_preimage' g h s

end
