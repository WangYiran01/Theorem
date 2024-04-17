import Theorem.example_separate.Ico_pow_choose_eq_pow_add_pow

open Nat

open Finset

open BigOperators

theorem Ico_pow_choose_eq_mul_pow(h: 2 ≤ n):  ∑ k in Ico 1 (n + 1), k ^ 2 * choose n k = n * (n + 1) * 2 ^ ( n - 2 )  := by
  have h1: 1 ≤ n := by linarith
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  rw[mul_add_mul_eq_mul]
