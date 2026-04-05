import Mathlib

variable {ι α β γ : Type*}

variable [CommRing α] [NormalizedGCDMonoid α]

theorem gcd_eq_of_dvd_sub {s : Finset β} {f g : β → α} {a : α}
    (h : ∀ x : β, x ∈ s → a ∣ f x - g x) :
    GCDMonoid.gcd a (s.gcd f) = GCDMonoid.gcd a (s.gcd g) := by
  classical
    revert h
    refine s.induction_on ?_ ?_
    · simp
    intro b s _ hi h
    rw [Finset.gcd_insert, Finset.gcd_insert, gcd_comm (f b), ← gcd_assoc,
      hi fun x hx ↦ h _ (mem_insert_of_mem hx), gcd_comm a, gcd_assoc,
      gcd_comm a (GCDMonoid.gcd _ _), gcd_comm (g b), gcd_assoc _ _ a, gcd_comm _ a]
    exact congr_arg _ (gcd_eq_of_dvd_sub_right (h _ (mem_insert_self _ _)))

