import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [Semiring R] [Semiring S] [AddCommMonoid A]

variable [Module R S] [Module S A] [Module R A] [IsScalarTower R S A]

theorem smul_mem_span_smul_of_mem {s : Set S} {t : Set A} {k : S} (hks : k ∈ span R s) {x : A}
    (hx : x ∈ t) : k • x ∈ span R (s • t) := span_induction (fun _ hc => subset_span <| Set.smul_mem_smul hc hx)
    (by rw [zero_smul]; exact zero_mem _)
    (fun c₁ c₂ _ _ ih₁ ih₂ => by rw [add_smul]; exact add_mem ih₁ ih₂)
    (fun b c _ hc => by rw [IsScalarTower.smul_assoc]; exact smul_mem _ _ hc) hks

