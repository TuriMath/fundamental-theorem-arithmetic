import Theorems.FundamentalTheoremArithmetic.A

/-!
# Fundamental theorem of arithmetic — proof (Euler)

From basic facts only: existence by strong induction using a prime divisor
(`Nat.exists_prime_and_dvd`), uniqueness by induction on one list using Euclid's lemma
(`Nat.Prime.dvd_mul`). Mathlib's `Nat.primeFactorsList` API is not used.
-/

namespace TuriMath.FundamentalTheoremArithmetic

theorem exists_primes : ∀ n : ℕ, n ≠ 0 → ∃ l : List ℕ, (∀ p ∈ l, p.Prime) ∧ l.prod = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h1 : n = 1
    · exact ⟨[], by simp, by simp [h1]⟩
    · obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd h1
      have hm : m ≠ 0 := fun h => hn (by simp [h])
      have hlt : m < p * m := by
        have := hp.two_le
        nlinarith [Nat.pos_of_ne_zero hm]
      obtain ⟨l, hl, e⟩ := ih m hlt hm
      refine ⟨p :: l, ?_, by simp [e]⟩
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hp
      · exact hl q hq

theorem prime_dvd_prod {p : ℕ} (hp : p.Prime) :
    ∀ {l : List ℕ}, p ∣ l.prod → ∃ q ∈ l, p ∣ q
  | [], h => by
      simp at h
      exact absurd h hp.one_lt.ne'
  | a :: t, h => by
      rw [List.prod_cons] at h
      rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact ⟨a, by simp, h⟩
      · obtain ⟨q, hq, hd⟩ := prime_dvd_prod hp h
        exact ⟨q, List.mem_cons_of_mem _ hq, hd⟩

theorem perm_of_prod_eq : ∀ (l₁ l₂ : List ℕ), (∀ p ∈ l₁, p.Prime) → (∀ p ∈ l₂, p.Prime) →
    l₁.prod = l₂.prod → List.Perm l₁ l₂
  | [], l₂, _, h₂, e => by
      cases l₂ with
      | nil => exact List.Perm.refl _
      | cons q t =>
        exfalso
        have hq := h₂ q (by simp)
        have : q ∣ 1 := by
          have : q ∣ (q :: t).prod := by simp
          simpa [← e] using this
        exact hq.one_lt.ne' (Nat.dvd_one.1 this)
  | p :: t, l₂, h₁, h₂, e => by
      have hp := h₁ p (by simp)
      have hd : p ∣ l₂.prod := by rw [← e]; simp
      obtain ⟨q, hq, hpq⟩ := prime_dvd_prod hp hd
      have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp (h₂ q hq)).1 hpq
      subst hpq'
      have hperm : List.Perm l₂ (p :: l₂.erase p) := List.perm_cons_erase hq
      have e2 : p * t.prod = p * (l₂.erase p).prod := by
        rw [← List.prod_cons, e, hperm.prod_eq, List.prod_cons]
      have e3 : t.prod = (l₂.erase p).prod := Nat.eq_of_mul_eq_mul_left hp.pos e2
      have ht : List.Perm t (l₂.erase p) :=
        perm_of_prod_eq t _ (fun x hx => h₁ x (by simp [hx]))
          (fun x hx => h₂ x ((List.erase_subset ..) hx)) e3
      exact (List.Perm.cons p ht).trans hperm.symm

theorem main : A.Statement := by
  intro n hn
  refine ⟨exists_primes n (by omega), fun l₁ l₂ h₁ e₁ h₂ e₂ => ?_⟩
  exact perm_of_prod_eq l₁ l₂ h₁ h₂ (e₁.trans e₂.symm)

end TuriMath.FundamentalTheoremArithmetic
