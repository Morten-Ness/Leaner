import Mathlib

variable {A : Type*}

variable [AddCommMonoid A] [PartialOrder A] [CanonicallyOrderedAdd A] [Sub A] [OrderedSub A]

variable [AddLeftReflectLE A]

variable [HasAntidiagonal A]

theorem filter_snd_eq_antidiagonal (n m : A) [DecidablePred (· = m)] [Decidable (m ≤ n)] :
    {x ∈ antidiagonal n | x.snd = m} = if m ≤ n then {(n - m, m)} else ∅ := by
  have : (fun x : A × A ↦ (x.snd = m)) ∘ Prod.swap = fun x : A × A ↦ x.fst = m := by
    ext; simp
  rw [← map_swap_antidiagonal, filter_map]
  simp [this, Finset.filter_fst_eq_antidiagonal, apply_ite (Finset.map _)]

