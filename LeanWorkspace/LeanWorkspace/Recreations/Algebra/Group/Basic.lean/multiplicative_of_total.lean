import Mathlib

variable {α β G M : Type*}

variable [Monoid β] (p r : α → α → Prop) [Std.Total r] (f : α → α → β)

theorem multiplicative_of_total (p : α → Prop) (hswap : ∀ {a b}, p a → p b → f a b * f b a = 1)
    (hmul : ∀ {a b c}, r a b → r b c → p a → p b → p c → f a c = f a b * f b c) {a b c : α}
    (pa : p a) (pb : p b) (pc : p c) : f a c = f a b * f b c := by
  apply multiplicative_of_symmetric_of_total (fun a b => p a ∧ p b) r f fun _ _ => And.symm
  · simp_rw [and_imp]; exact @hswap
  · exact fun rab rbc pab _pbc pac => hmul rab rbc pab.1 pab.2 pac.2
  exacts [⟨pa, pb⟩, ⟨pb, pc⟩, ⟨pa, pc⟩]

