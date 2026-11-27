import Mathlib

/-!
# Fundamental theorem of arithmetic — statement B (Gauss, blind to A)

Source (Wikipedia, "Fundamental theorem of arithmetic", lead sentence; Wiedijk's 100, item 80):
> every integer greater than 1 is either prime or can be represented uniquely as a product of
> prime numbers, up to the order of the factors.

Mapping, source → Lean:
* "integer greater than 1"            → `n : ℕ` with `1 < n` (the integers > 1 are exactly these naturals)
* "prime number"                      → `IsPrimeNum p`: `2 ≤ p` and its only divisors are `1` and `p`
                                        (elementary on purpose, not `Nat.Prime`)
* "a product of prime numbers"        → a finite list `l : List ℕ` of primes with `l.prod = n`
                                        (repeats allowed, so `12 = 2 * 2 * 3` is `[2, 2, 3]`)
* "either prime or …"                 → a prime `p` is the one-factor product `[p]`, so existence is
                                        asked for every `n > 1` with no case split
* "can be represented"                → `Existence`: some such list exists
* "uniquely … up to the order"        → `Uniqueness`: any two such lists for the same `n` contain each
                                        number the same number of times (`List.count` agrees for all `q`),
                                        i.e. they differ only by reordering, multiplicity counted
* the theorem                         → `Statement := Existence ∧ Uniqueness`
-/

namespace TuriMath.FundamentalTheoremArithmetic.B

/-- `p` is prime: at least 2, and every divisor of `p` is `1` or `p`. -/
def IsPrimeNum (p : ℕ) : Prop := 2 ≤ p ∧ ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p

/-- Every integer `n > 1` is a product of (finitely many, possibly repeated) primes. -/
def Existence : Prop :=
  ∀ n : ℕ, 1 < n → ∃ l : List ℕ, (∀ p ∈ l, IsPrimeNum p) ∧ l.prod = n

/-- Two prime factorizations of the same `n > 1` use each number equally often. -/
def Uniqueness : Prop :=
  ∀ n : ℕ, 1 < n → ∀ l₁ l₂ : List ℕ,
    (∀ p ∈ l₁, IsPrimeNum p) → l₁.prod = n →
    (∀ p ∈ l₂, IsPrimeNum p) → l₂.prod = n →
    ∀ q : ℕ, l₁.count q = l₂.count q

/-- The fundamental theorem of arithmetic. -/
def Statement : Prop := Existence ∧ Uniqueness

/-! ## Sanity section -/

/-- `IsPrimeNum` agrees with Mathlib's `Nat.Prime` (so it is neither vacuous nor too weak). -/
theorem isPrimeNum_iff (p : ℕ) : IsPrimeNum p ↔ p.Prime := Nat.prime_def.symm

-- The hypotheses can all hold at once: n = 12 > 1 with factorization [2, 2, 3] (2·2·3 = 12).
example : 1 < 12 ∧ (∀ p ∈ [2, 2, 3], IsPrimeNum p) ∧ [2, 2, 3].prod = 12 := by
  refine ⟨by norm_num, ?_, by norm_num⟩
  intro p hp
  rw [isPrimeNum_iff]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num

-- Two factorizations of the same n at once: 12 = 2·2·3 = 3·2·2; the uniqueness conclusion holds.
example : ∀ q : ℕ, [2, 2, 3].count q = [3, 2, 2].count q := by
  intro q; simp [List.count_cons]; omega

-- A prime is its own one-factor product: n = 7, l = [7].
example : (∀ p ∈ [7], IsPrimeNum p) ∧ [7].prod = 7 := by
  refine ⟨?_, by norm_num⟩
  intro p hp
  rw [List.mem_singleton] at hp
  subst hp
  rw [isPrimeNum_iff]; norm_num

-- Uniqueness really needs primality: 12 = 2·6 = 3·4 but the counts differ (6 and 4 are not prime).
example : [2, 6].prod = [3, 4].prod ∧ [2, 6].count 2 ≠ [3, 4].count 2 := by decide
example : ¬ IsPrimeNum 6 := by rw [isPrimeNum_iff]; norm_num

-- Multiplicity matters: [2, 3] and [2, 2, 3] are not the same factorization (count of 2 differs).
example : [2, 3].count 2 ≠ [2, 2, 3].count 2 := by decide

end TuriMath.FundamentalTheoremArithmetic.B
