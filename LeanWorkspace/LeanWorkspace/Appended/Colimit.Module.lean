import Mathlib

section

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)] (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

variable [DecidableEq ι]

theorem of_f {i j hij x} : Module.DirectLimit.of R ι G f j (f i j hij x) = Module.DirectLimit.of R ι G f i x := (AddCon.eq _).mpr <| .symm <| .of _ _ (.of_map _ _)

end

section

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)] (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

variable [DecidableEq ι]

theorem exists_of [Nonempty ι] [IsDirectedOrder ι] (z : Module.DirectLimit G f) :
    ∃ i x, Module.DirectLimit.of R ι G f i x = z := Nonempty.elim (by infer_instance) fun ind : ι ↦
    Quotient.inductionOn' z fun z ↦
      DirectSum.induction_on z ⟨ind, 0, map_zero _⟩ (fun i x ↦ ⟨i, x, rfl⟩)
        fun p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩ ↦
        let ⟨k, hik, hjk⟩ := exists_ge_ge i j
        ⟨k, f i k hik x + f j k hjk y, by
          rw [map_add, Module.DirectLimit.of_f, Module.DirectLimit.of_f, ihx, ihy]
          rfl ⟩

end

section

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)] (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

variable [DecidableEq ι]

theorem exists_of₂ [Nonempty ι] [IsDirectedOrder ι] (z w : Module.DirectLimit G f) :
    ∃ i x y, Module.DirectLimit.of R ι G f i x = z ∧ Module.DirectLimit.of R ι G f i y = w := have ⟨i, x, hx⟩ := Module.DirectLimit.exists_of z
  have ⟨j, y, hy⟩ := Module.DirectLimit.exists_of w
  have ⟨k, hik, hjk⟩ := exists_ge_ge i j
  ⟨k, f i k hik x, f j k hjk y, by rw [Module.DirectLimit.of_f, hx], by rw [Module.DirectLimit.of_f, hy]⟩

end

section

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable (G) [∀ i, AddCommMonoid (G i)]

variable (f : ∀ i j, i ≤ j → G i →+ G j)

variable [DecidableEq ι]

variable (P : Type*) [AddCommMonoid P]

variable (g : ∀ i, G i →+ P)

variable (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

theorem lift_of (i x) : AddCommGroup.DirectLimit.lift G f P g Hg (AddCommGroup.DirectLimit.of G f i x) = g i x := Module.DirectLimit.lift_of
    -- Note: had to make these arguments explicit https://github.com/leanprover-community/mathlib4/pull/8386
    (f := fun i j hij ↦ (f i j hij).toNatLinearMap)
    (fun i ↦ (g i).toNatLinearMap)
    Hg
    x

end

section

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)] (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

variable [DecidableEq ι]

variable [Nonempty ι] [IsDirectedOrder ι] [DirectedSystem G (f · · ·)]

theorem linearEquiv_of {i g} : Module.DirectLimit.linearEquiv _ _ (Module.DirectLimit.of _ _ G f i g) = ⟦⟨i, g⟩⟧ := by
  simp [Module.DirectLimit.linearEquiv]; rfl

end
