import Mathlib.Data.Nat.Choose.Sum

#align_import data.nat.choose.sum from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

open Nat


theorem idt1_Pascal's_Recurrence(h1:1 ≤ n)(h2:1 ≤ k) : choose n k = choose (n-1) k  + choose (n-1) (k-1) := by
  have choose_eq_choose_sub_add :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[choose_eq_choose_sub_add]
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  have choose_sub_eq_choose_sub_add : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]


theorem idt1_Pascal's_Recurrence_from_0_to_0(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(gol:  choose n k = choose (n - 1) k + choose (n - 1) (k - 1)) :
   choose n k = choose (n - 1) k + choose (n - 1) (k - 1) := by
  have choose_eq_choose_sub_add :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  apply gol

theorem idt1_Pascal's_Recurrence_from_0_to_1(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(gol:  choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) k + choose (n - 1) (k - 1)) :
   choose n k = choose (n - 1) k + choose (n - 1) (k - 1) := by
  have choose_eq_choose_sub_add :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[choose_eq_choose_sub_add]
  apply gol

theorem idt1_Pascal's_Recurrence_from_0_to_2(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(gol:  choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k) :
   choose n k = choose (n - 1) k + choose (n - 1) (k - 1) := by
  have choose_eq_choose_sub_add :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[choose_eq_choose_sub_add]
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  apply gol

theorem idt1_Pascal's_Recurrence_from_0_to_3(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(gol:  choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k) :
   choose n k = choose (n - 1) k + choose (n - 1) (k - 1) := by
  have choose_eq_choose_sub_add :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[choose_eq_choose_sub_add]
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  have choose_sub_eq_choose_sub_add : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by rw[Nat.sub_add_cancel h2]
  apply gol

theorem idt1_Pascal's_Recurrence_from_0_to_4(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k) :
   choose n k = choose (n - 1) k + choose (n - 1) (k - 1) := by
  have choose_eq_choose_sub_add :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[choose_eq_choose_sub_add]
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  have choose_sub_eq_choose_sub_add : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]

theorem idt1_Pascal's_Recurrence_from_1_to_1(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : choose n k = choose (n - 1 + 1) (k - 1 + 1))(gol:  choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) k + choose (n - 1) (k - 1)) :
   choose n k = choose (n - 1) k + choose (n - 1) (k - 1) := by
  rw[choose_eq_choose_sub_add]
  apply gol

theorem idt1_Pascal's_Recurrence_from_1_to_2(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : choose n k = choose (n - 1 + 1) (k - 1 + 1))(gol:  choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k) :
   choose n k = choose (n - 1) k + choose (n - 1) (k - 1) := by
  rw[choose_eq_choose_sub_add]
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  apply gol

theorem idt1_Pascal's_Recurrence_from_1_to_3(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : choose n k = choose (n - 1 + 1) (k - 1 + 1))(gol:  choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k) :
   choose n k = choose (n - 1) k + choose (n - 1) (k - 1) := by
  rw[choose_eq_choose_sub_add]
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  have choose_sub_eq_choose_sub_add : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by rw[Nat.sub_add_cancel h2]
  apply gol

theorem idt1_Pascal's_Recurrence_from_1_to_4(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : choose n k = choose (n - 1 + 1) (k - 1 + 1)) :
   choose n k = choose (n - 1) k + choose (n - 1) (k - 1) := by
  rw[choose_eq_choose_sub_add]
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  have choose_sub_eq_choose_sub_add : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]

theorem idt1_Pascal's_Recurrence_from_2_to_2(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : choose n k = choose (n - 1 + 1) (k - 1 + 1))(gol:  choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k) :
   choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) k + choose (n - 1) (k - 1) := by
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  apply gol

theorem idt1_Pascal's_Recurrence_from_2_to_3(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : choose n k = choose (n - 1 + 1) (k - 1 + 1))(gol:  choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k) :
   choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) k + choose (n - 1) (k - 1) := by
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  have choose_sub_eq_choose_sub_add : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by rw[Nat.sub_add_cancel h2]
  apply gol

theorem idt1_Pascal's_Recurrence_from_2_to_4(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : choose n k = choose (n - 1 + 1) (k - 1 + 1)) :
   choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) k + choose (n - 1) (k - 1) := by
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  have choose_sub_eq_choose_sub_add : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]

theorem idt1_Pascal's_Recurrence_from_3_to_3(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : choose n k = choose (n - 1 + 1) (k - 1 + 1))(gol:  choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k) :
   choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k := by
  have choose_sub_eq_choose_sub_add : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by rw[Nat.sub_add_cancel h2]
  apply gol

theorem idt1_Pascal's_Recurrence_from_3_to_4(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : choose n k = choose (n - 1 + 1) (k - 1 + 1)) :
   choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k := by
  have choose_sub_eq_choose_sub_add : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]

theorem idt1_Pascal's_Recurrence_from_4_to_4(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : choose n k = choose (n - 1 + 1) (k - 1 + 1))(choose_sub_eq_choose_sub_add : choose (n - 1) k = choose (n - 1) (k - 1 + 1)) :
   choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k := by
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]

