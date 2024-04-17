import Mathlib.Data.Nat.Choose.Basic

#align_import data.nat.choose.sum from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

open Nat




theorem idt6_Absorption_Idt {n k : ℕ} (hkn : k ≤ n) (hsk : 1 ≤ k) :
    k * choose n k  = n * choose (n - 1) (k - 1) := by
      have choose_mul_eq_choose_mul :  choose k 1  * choose n k= choose n 1 * choose (n - 1) (k - 1)  := by rw[mul_comm, choose_mul hkn hsk]
      rw[choose_one_right, choose_one_right] at choose_mul_eq_choose_mul
      rw[choose_mul_eq_choose_mul]


theorem idt6_Absorption_Idt_from_0_to_0(n k : ℕ)(hkn : k ≤ n)(hsk : 1 ≤ k)(gol:  k * choose n k = n * choose (n - 1) (k - 1)) :
   k * choose n k = n * choose (n - 1) (k - 1) := by
  have choose_mul_eq_choose_mul :  choose k 1  * choose n k= choose n 1 * choose (n - 1) (k - 1)  := by rw[mul_comm, choose_mul hkn hsk]
  apply gol

theorem idt6_Absorption_Idt_from_0_to_1(n k : ℕ)(hkn : k ≤ n)(hsk : 1 ≤ k)(gol:  k * choose n k = n * choose (n - 1) (k - 1)) :
   k * choose n k = n * choose (n - 1) (k - 1) := by
  have choose_mul_eq_choose_mul :  choose k 1  * choose n k= choose n 1 * choose (n - 1) (k - 1)  := by rw[mul_comm, choose_mul hkn hsk]
  rw[choose_one_right, choose_one_right] at choose_mul_eq_choose_mul
  apply gol

theorem idt6_Absorption_Idt_from_0_to_2(n k : ℕ)(hkn : k ≤ n)(hsk : 1 ≤ k) :
   k * choose n k = n * choose (n - 1) (k - 1) := by
  have choose_mul_eq_choose_mul :  choose k 1  * choose n k= choose n 1 * choose (n - 1) (k - 1)  := by rw[mul_comm, choose_mul hkn hsk]
  rw[choose_one_right, choose_one_right] at choose_mul_eq_choose_mul
  rw[choose_mul_eq_choose_mul]

theorem idt6_Absorption_Idt_from_1_to_1(n k : ℕ)(hkn : k ≤ n)(hsk : 1 ≤ k)(choose_mul_eq_choose_mul : choose k 1 * choose n k = choose n 1 * choose (n - 1) (k - 1))(gol:  k * choose n k = n * choose (n - 1) (k - 1)) :
   k * choose n k = n * choose (n - 1) (k - 1) := by
  rw[choose_one_right, choose_one_right] at choose_mul_eq_choose_mul
  apply gol

theorem idt6_Absorption_Idt_from_1_to_2(n k : ℕ)(hkn : k ≤ n)(hsk : 1 ≤ k)(choose_mul_eq_choose_mul : choose k 1 * choose n k = choose n 1 * choose (n - 1) (k - 1)) :
   k * choose n k = n * choose (n - 1) (k - 1) := by
  rw[choose_one_right, choose_one_right] at choose_mul_eq_choose_mul
  rw[choose_mul_eq_choose_mul]

theorem idt6_Absorption_Idt_from_2_to_2(n k : ℕ)(hkn : k ≤ n)(hsk : 1 ≤ k)(choose_mul_eq_choose_mul : k * choose n k = n * choose (n - 1) (k - 1)) :
   k * choose n k = n * choose (n - 1) (k - 1) := by
  rw[choose_mul_eq_choose_mul]

