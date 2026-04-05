import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*} (s : Finset ι) {ι₂ : Type*} (s₂ : Finset ι₂)

variable {k} in

theorem centroid_eq_of_inj_on_of_image_eq {p : ι → P}
    (hi : ∀ i ∈ s, ∀ j ∈ s, p i = p j → i = j) {p₂ : ι₂ → P}
    (hi₂ : ∀ i ∈ s₂, ∀ j ∈ s₂, p₂ i = p₂ j → i = j) (he : p '' ↑s = p₂ '' ↑s₂) :
    s.centroid k p = s₂.centroid k p₂ := by
  classical rw [Finset.centroid_eq_centroid_image_of_inj_on s k hi rfl,
      Finset.centroid_eq_centroid_image_of_inj_on s₂ k hi₂ he]

