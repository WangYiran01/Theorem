import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat

theorem choose_mul_eq_mul_sub_div {n k: ℕ} :
 (((1/(k+1)) : ℝ) * choose n k) = (1/(n+1)) * choose (n+1) (k+1) := by
  have h1 : (k : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero k
  have h2 : (n + 1) * (k + 1) * ((1 / (n+1)) : ℝ) * (Nat.choose (n + 1) (k + 1))
      = (k + 1) * ((n + 1) * (1 / (n+1)) * (Nat.choose (n + 1) (k + 1))) := by
      rw [←mul_assoc]
      congr 1
      rw [←mul_assoc]
      congr 1
      rw [mul_comm]
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    rw [h2]
    rw [←mul_assoc]
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  rw [mul_right_inj' h8] at h
  assumption
