import Mathlib

variable {ι : Type*} [Preorder ι] (G : ι → Type*)

variable [∀ i, CommRing (G i)]

variable (f : ∀ i j, i ≤ j → G i → G j)

variable (P : Type*) [CommRing P]

variable (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

variable (f' : ∀ i j, i ≤ j → G i →+* G j)

variable {f : ∀ i j, i ≤ j → G i →+* G j}

variable {G' : ι → Type*} [∀ i, CommRing (G' i)]

variable {f' : ∀ i j, i ≤ j → G' i →+* G' j}

variable {G'' : ι → Type*} [∀ i, CommRing (G'' i)]

variable {f'' : ∀ i j, i ≤ j → G'' i →+* G'' j}

theorem map_comp (g₁ : (i : ι) → G i →+* G' i) (g₂ : (i : ι) → G' i →+* G'' i)
    (hg₁ : ∀ i j h, (g₁ j).comp (f i j h) = (f' i j h).comp (g₁ i))
    (hg₂ : ∀ i j h, (g₂ j).comp (f' i j h) = (f'' i j h).comp (g₂ i)) :
    ((Ring.DirectLimit.map g₂ hg₂).comp (Ring.DirectLimit.map g₁ hg₁) :
      Ring.DirectLimit G (fun _ _ h ↦ f _ _ h) →+* Ring.DirectLimit G'' fun _ _ h ↦ f'' _ _ h) =
    (Ring.DirectLimit.map (fun i ↦ (g₂ i).comp (g₁ i)) fun i j h ↦ by
      rw [RingHom.comp_assoc, hg₁ i, ← RingHom.comp_assoc, hg₂ i, RingHom.comp_assoc] :
      Ring.DirectLimit G (fun _ _ h ↦ f _ _ h) →+* Ring.DirectLimit G'' fun _ _ h ↦ f'' _ _ h) := by
  ext; simp

