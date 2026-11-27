import Mathlib

/-!
# Fundamental theorem of arithmetic — statement A (Noether)

Source (Wikipedia, "Fundamental theorem of arithmetic", lead sentence; Wiedijk 100, item 80):
> every integer greater than 1 is either prime or can be represented uniquely as a product of
> prime numbers, up to the order of the factors.
-/

namespace TuriMath.FundamentalTheoremArithmetic.A

/-- **Fundamental theorem of arithmetic.**

Mapping from the source quote to the Lean:
* "every integer greater than 1" ↦ `∀ n : ℕ, 1 < n → …`. ℕ, not ℤ: the integers greater than 1
  are exactly the naturals greater than 1, and `Nat.Prime` is Mathlib's notion of prime number.
* "prime numbers" ↦ every entry `p` of a factor list satisfies `p.Prime` (`Nat.Prime`).
* "a product of prime numbers" ↦ a `List ℕ` whose `List.prod` is `n`. A list, not a set, so
  repeated primes count with multiplicity.
* "is either prime or …" ↦ no separate disjunct: a prime `p` is the one-factor product `[p]`,
  so existence and uniqueness are both asserted for every `n > 1` (as the issue's notes require).
  This is stronger than the bare disjunction, which would claim nothing about uniqueness for primes.
* "can be represented" (existence) ↦ first conjunct: `∃ l, (∀ p ∈ l, p.Prime) ∧ l.prod = n`.
* "uniquely …, up to the order of the factors" ↦ second conjunct: any two prime-factor lists
  with product `n` are permutations of each other, `List.Perm l₁ l₂`.
-/
def Statement : Prop :=
  ∀ n : ℕ, 1 < n →
    (∃ l : List ℕ, (∀ p ∈ l, p.Prime) ∧ l.prod = n) ∧
    (∀ l₁ l₂ : List ℕ,
      (∀ p ∈ l₁, p.Prime) → l₁.prod = n →
      (∀ p ∈ l₂, p.Prime) → l₂.prod = n →
      List.Perm l₁ l₂)

/-! ## Sanity section

The only outer hypothesis is `1 < n`; it is satisfiable. The hypotheses of the uniqueness
conjunct (a list of primes with product `n`) can also all hold at once, for the same `n`. -/

example : ∃ n : ℕ, 1 < n := ⟨2, by norm_num⟩

example : ∃ n : ℕ, 1 < n ∧ ∃ l₁ l₂ : List ℕ,
    (∀ p ∈ l₁, p.Prime) ∧ l₁.prod = n ∧ (∀ p ∈ l₂, p.Prime) ∧ l₂.prod = n :=
  ⟨6, by norm_num, [2, 3], [3, 2], by simp [Nat.prime_two, Nat.prime_three]⟩

end TuriMath.FundamentalTheoremArithmetic.A
