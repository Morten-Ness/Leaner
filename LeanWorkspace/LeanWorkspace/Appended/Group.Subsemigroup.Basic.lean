import Mathlib

section

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ Subsemigroup.closure s) : Subsemigroup.closure s = S := le_antisymm (Subsemigroup.closure_le.2 h₁) h₂

end

section

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem closure_induction {p : (x : M) → x ∈ Subsemigroup.closure s → Prop}
    (mem : ∀ (x) (h : x ∈ s), p x (Subsemigroup.subset_closure h))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy)) {x} (hx : x ∈ Subsemigroup.closure s) :
    p x hx := let S : Subsemigroup M :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, mul _ _ _ _ hpx hpy⟩ }
  Subsemigroup.closure_le (S := S) |>.mpr (fun y hy ↦ ⟨Subsemigroup.subset_closure hy, mem y hy⟩) hx |>.elim fun _ ↦ id

end

section

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem closure_induction₂ {p : (x y : M) → x ∈ Subsemigroup.closure s → y ∈ Subsemigroup.closure s → Prop}
    (mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), p x y (Subsemigroup.subset_closure hx) (Subsemigroup.subset_closure hy))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz, p z x hz hx → p z y hz hy → p z (x * y) hz (mul_mem hx hy))
    {x y : M} (hx : x ∈ Subsemigroup.closure s) (hy : y ∈ Subsemigroup.closure s) : p x y hx hy := by
  induction hx using Subsemigroup.closure_induction with
  | mem z hz => induction hy using Subsemigroup.closure_induction with
    | mem _ h => exact mem _ _ hz h
    | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ hy h₁ h₂

end

section

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem coe_iInf {ι : Sort*} {S : ι → Subsemigroup M} : (↑(⨅ i, S i) : Set M) = ⋂ i, S i := by
  simp only [iInf, Subsemigroup.coe_sInf, Set.biInter_range]

end

section

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable [Mul N]

theorem eqOn_closure {f g : M →ₙ* N} {s : Set M} (h : Set.EqOn f g s) :
    Set.EqOn f g (Subsemigroup.closure s) := show Subsemigroup.closure s ≤ f.eqLocus g from Subsemigroup.closure_le.2 h

end

section

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem iSup_eq_closure {ι : Sort*} (p : ι → Subsemigroup M) :
    ⨆ i, p i = Subsemigroup.closure (⋃ i, (p i : Set M)) := by
  simp_rw [Subsemigroup.closure_iUnion, Subsemigroup.closure_eq]

end

section

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem mem_iInf {ι : Sort*} {S : ι → Subsemigroup M} {x : M} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
  simp only [iInf, Subsemigroup.mem_sInf, Set.forall_mem_range]

end

section

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem mem_iSup {ι : Sort*} (p : ι → Subsemigroup M) {m : M} :
    (m ∈ ⨆ i, p i) ↔ ∀ N, (∀ i, p i ≤ N) → m ∈ N := by
  rw [← Subsemigroup.closure_singleton_le_iff_mem, le_iSup_iff]
  simp only [Subsemigroup.closure_singleton_le_iff_mem]

end
