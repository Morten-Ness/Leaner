import Mathlib

section

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem mul_sInter_subset (s : Set α) (T : Set (Set α)) :
    s * ⋂₀ T ⊆ ⋂ t ∈ T, s * t := image2_sInter_right_subset s T (fun a b => a * b)

end

section

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem sInter_mul_subset (S : Set (Set α)) (t : Set α) :
    ⋂₀ S * t ⊆ ⋂ s ∈ S, s * t := image2_sInter_left_subset S t (fun a b => a * b)

end

section

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

theorem sInter_smul_subset (S : Set (Set α)) (t : Set β) : ⋂₀ S • t ⊆ ⋂ s ∈ S, s • t := image2_sInter_left_subset S t (fun a x => a • x)

end

section

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

theorem smul_sInter_subset (s : Set α) (T : Set (Set β)) : s • ⋂₀ T ⊆ ⋂ t ∈ T, s • t := image2_sInter_right_subset s T (fun a x => a • x)

end

section

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

theorem smul_set_sUnion (a : α) (S : Set (Set β)) : a • ⋃₀ S = ⋃ s ∈ S, a • s := by
  rw [sUnion_eq_biUnion, Set.smul_set_iUnion₂]

end
