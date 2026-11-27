import Theorems.FundamentalTheoremArithmetic.A
import Theorems.FundamentalTheoremArithmetic.B

/-!
# Fundamental theorem of arithmetic — A ↔ B (Euler)

Matches the two statements: `IsPrimeNum` is `Nat.Prime`, and equal counts are `List.Perm`.
Each direction uses the other statement as a hypothesis; neither is proved from Mathlib's theorem.
-/

namespace TuriMath.FundamentalTheoremArithmetic

theorem equiv : A.Statement ↔ B.Statement := by
  constructor
  · intro h
    refine ⟨fun n hn => ?_, fun n hn l₁ l₂ h₁ e₁ h₂ e₂ q => ?_⟩
    · obtain ⟨l, hl, e⟩ := (h n hn).1
      exact ⟨l, fun p hp => (B.isPrimeNum_iff p).2 (hl p hp), e⟩
    · exact ((h n hn).2 l₁ l₂ (fun p hp => (B.isPrimeNum_iff p).1 (h₁ p hp)) e₁
        (fun p hp => (B.isPrimeNum_iff p).1 (h₂ p hp)) e₂).count_eq q
  · intro h n hn
    refine ⟨?_, fun l₁ l₂ h₁ e₁ h₂ e₂ => ?_⟩
    · obtain ⟨l, hl, e⟩ := h.1 n hn
      exact ⟨l, fun p hp => (B.isPrimeNum_iff p).1 (hl p hp), e⟩
    · exact List.perm_iff_count.2 (h.2 n hn l₁ l₂ (fun p hp => (B.isPrimeNum_iff p).2 (h₁ p hp)) e₁
        (fun p hp => (B.isPrimeNum_iff p).2 (h₂ p hp)) e₂)

end TuriMath.FundamentalTheoremArithmetic
