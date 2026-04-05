import Mathlib

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable (G) [∀ i, AddCommMonoid (G i)]

variable (f : ∀ i j, i ≤ j → G i →+ G j)

variable [DecidableEq ι]

variable (P : Type*) [AddCommMonoid P]

variable (g : ∀ i, G i →+ P)

variable (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

variable {G' : ι → Type*} [∀ i, AddCommMonoid (G' i)]

variable {f' : ∀ i j, i ≤ j → G' i →+ G' j}

variable {G'' : ι → Type*} [∀ i, AddCommMonoid (G'' i)]

variable {f'' : ∀ i j, i ≤ j → G'' i →+ G'' j}

theorem map_comp (g₁ : (i : ι) → G i →+ G' i) (g₂ : (i : ι) → G' i →+ G'' i)
    (hg₁ : ∀ i j h, (g₁ j).comp (f i j h) = (f' i j h).comp (g₁ i))
    (hg₂ : ∀ i j h, (g₂ j).comp (f' i j h) = (f'' i j h).comp (g₂ i)) :
    ((AddCommGroup.DirectLimit.map g₂ hg₂).comp (AddCommGroup.DirectLimit.map g₁ hg₁) :
      AddCommGroup.DirectLimit G f →+ AddCommGroup.DirectLimit G'' f'') =
    (AddCommGroup.DirectLimit.map (fun i ↦ (g₂ i).comp (g₁ i)) fun i j h ↦ by
      rw [AddMonoidHom.comp_assoc, hg₁ i, ← AddMonoidHom.comp_assoc, hg₂ i,
        AddMonoidHom.comp_assoc] :
      AddCommGroup.DirectLimit G f →+ AddCommGroup.DirectLimit G'' f'') := by
  ext; simp

