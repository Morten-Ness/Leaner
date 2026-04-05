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

theorem congr_symm_apply_of (e : (i : ι) → G i ≃+ G' i)
    (he : ∀ i j h, (e j).toAddMonoidHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G' i) :
    (AddCommGroup.DirectLimit.congr e he).symm (AddCommGroup.DirectLimit.of G' f' i g) = AddCommGroup.DirectLimit.of G f i ((e i).symm g) := by
  simp only [AddCommGroup.DirectLimit.congr, AddMonoidHom.toAddEquiv_symm_apply, map_apply_of, AddMonoidHom.coe_coe]

