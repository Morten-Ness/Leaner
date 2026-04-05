import Mathlib

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable (G) [∀ i, AddCommMonoid (G i)]

variable (f : ∀ i j, i ≤ j → G i →+ G j)

variable [DecidableEq ι]

variable (P : Type*) [AddCommMonoid P]

variable (g : ∀ i, G i →+ P)

variable (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

theorem lift_comp_of (F : AddCommGroup.DirectLimit G f →+ P) :
    AddCommGroup.DirectLimit.lift G f _ (fun i ↦ F.comp <| AddCommGroup.DirectLimit.of G f i) (fun i j hij x ↦ by simp) = F := by
  ext; simp

