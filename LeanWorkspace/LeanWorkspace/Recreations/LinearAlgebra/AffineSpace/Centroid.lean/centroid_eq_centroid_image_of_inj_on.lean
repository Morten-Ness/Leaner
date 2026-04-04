import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*} (s : Finset ι) {ι₂ : Type*} (s₂ : Finset ι₂)

variable {k} in

theorem centroid_eq_centroid_image_of_inj_on {p : ι → P}
    (hi : ∀ i ∈ s, ∀ j ∈ s, p i = p j → i = j) {ps : Set P} [Fintype ps]
    (hps : ps = p '' ↑s) : s.centroid k p = (univ : Finset ps).centroid k fun x => (x : P) := by
  let f : p '' ↑s → ι := fun x => x.property.choose
  have hf : ∀ x, f x ∈ s ∧ p (f x) = x := fun x => x.property.choose_spec
  let f' : ps → ι := fun x => f ⟨x, hps ▸ x.property⟩
  have hf' : ∀ x, f' x ∈ s ∧ p (f' x) = x := fun x => hf ⟨x, hps ▸ x.property⟩
  have hf'i : Function.Injective f' := by
    intro x y h
    rw [Subtype.ext_iff, ← (hf' x).2, ← (hf' y).2, h]
  let f'e : ps ↪ ι := ⟨f', hf'i⟩
  have hu : Finset.univ.map f'e = s := by
    ext x
    rw [mem_map]
    constructor
    · rintro ⟨i, _, rfl⟩
      exact (hf' i).1
    · intro hx
      use ⟨p x, hps.symm ▸ Set.mem_image_of_mem _ hx⟩, mem_univ _
      refine hi _ (hf' _).1 _ hx ?_
      rw [(hf' _).2]
  rw [← hu, Finset.centroid_map]
  congr with x
  change p (f' x) = ↑x
  rw [(hf' x).2]

