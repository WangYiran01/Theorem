import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem h_pow_zero_mul_add:
 ((-1 : ℝ)^0 * (choose (n-1) 0 : ℝ) * (m / (m+0)) + ∑ k in Ico 1 n, (-1 : ℝ)^k * ((choose (n-1) k) : ℝ) * (m / (m+k))) =
  ((-1 : ℝ)^0 * (choose (n-1) 0 : ℝ) * (m / (m+0)) + ∑ k in Ico (0+1) n, (-1 : ℝ)^k * ((choose (n-1) k) : ℝ) * (m / (m+k))):= by
    congr 1


theorem h_pow_zero_mul_add_from_0_to_0(n : ℕ)(m : ℝ) :
   (-1 : ℝ) ^ 0 * ↑(Nat.choose (n - 1) 0) * (m / (m + 0)) +
      ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)) =
    (-1 : ℝ) ^ 0 * ↑(Nat.choose (n - 1) 0) * (m / (m + 0)) +
      ∑ k in Ico (0 + 1) n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)) := by
  congr 1

