-- Author: Uğur Y. Yavuz
-- CAS CS 511: Formal Methods for High-Assurance Software Engineering
-- Boston University, Fall 2023
-- Instructor: Prof. Assaf Kfoury
-- Homework #1

import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

-- Problem 3A.
lemma Deduc21 {p q r : Prop} (h_pqr : (p ∧ q) → r) : p → (q → r) := by
  intro h_p 
  intro h_q 
  have h_pq : p ∧ q := by 
    apply And.intro h_p h_q
  apply h_pqr h_pq

-- Problem 3B.
lemma Deduc23 {p q r : Prop} (h_pqr : p → (q → r)) : (p → q) → (p → r) := by
  intro h_pq
  intro h_p
  have h_q : q := by apply h_pq h_p
  have h_qr : q → r := by apply h_pqr h_p
  apply h_qr h_q

-- Problem 3C.
axiom notnotE {p : Prop} (h : ¬¬p) : p
lemma Deduc24 {p q r : Prop} (h_pqr : (p ∧ ¬q) → r) (h_nr : ¬r) (h_p : p) : q := by
  have h_nnq : ¬¬q := by
    intro h_nq
    have h_pnq : p ∧ ¬q := by apply And.intro h_p h_nq
    have h_r : r := by apply h_pqr h_pnq
    have h_bot : False := by apply h_nr h_r
    exact h_bot
  apply notnotE h_nnq

-- 3C, alternatively
lemma Deduc242 {p q r : Prop} (h_pqr : (p ∧ ¬q) → r) (h_nr : ¬r) (h_p : p) : q := by
  have h_nnq : ¬¬q := by 
    intro h_nq
    have h_pnq : p ∧ ¬q := by apply And.intro h_p h_nq
    have h_r : r := by apply h_pqr h_pnq
    contradiction
  apply notnotE h_nnq
  
-- Problem 4A.
lemma Exp1 {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 := calc
  a = 2 * b + 5 := by rw[h1]
  _ = 2 * 3 + 5 := by rw[h2]
  _ = 11 := by ring

-- Problem 4B.
lemma Exp2 {x : ℤ} (h1 : x + 4 = 2) : x = -2 := calc
  x = (x + 4) - 4 := by ring
  _ = 2 - 4 := by rw[h1]
  _ = -2 := by ring

-- Problem 4C.
lemma Exp3 {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := calc
  a = (a - 5 * b) + 5 * b := by ring
  _ = 4 + 5 * b := by rw[h1]
  _ = -6 + 5 * (b + 2) := by ring
  _ = -6 + 5 * 3 := by rw[h2]
  _ = 9 := by ring
