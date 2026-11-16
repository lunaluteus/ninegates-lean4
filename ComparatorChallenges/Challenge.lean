/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Standard.Defs
public import Ninegates.Standard.OneDefs
public import Ninegates.Minimal.Defs
public import Ninegates.Minimal.Alternating.Defs

/-! Trusted statements for the structural library. Only the selected theorem
proofs are holes; every definition and parameter is fixed by these imports.
Do not import the solution or proof modules into this file. -/

@[expose] public section

namespace ComparatorChallenges

open Mahjong Mahjong.VirtualHand

theorem virtual_criterion (n : ℕ) (c : VirtualHand n) :
    VirtuallyMeldable c ↔ (size c : ZMod 3) = 0 ∧ (rankSum c : ZMod 3) = 0 :=
  by sorry

theorem eight_family (n : ℕ) (order : 2 ≤ n) (c : VirtualHand n) :
    IsFullWait (n + 1) c ↔ Standard.EightFamily c :=
  by sorry

theorem live_uniqueness (n : ℕ) (order : 2 ≤ n) (c : VirtualHand n) :
    IsLiveFullWait 4 (n + 1) c ↔ c = Standard.A n :=
  by sorry

theorem order_one (c : VirtualHand 1) :
    IsFullWait 2 c ↔ Standard.OrderOneFamily c :=
  by sorry

theorem minimal_eight_family (n : ℕ) (order : 2 ≤ n) (c : VirtualHand n) :
    IsMinimalFullWait (n + 1) c ↔ Standard.EightFamily c :=
  by sorry

theorem minimal_order_one (m : ℕ) (c : VirtualHand 1) :
    IsMinimalFullWait m c ↔ m = 2 ∧ Standard.OrderOneFamily c :=
  by sorry

theorem maximal_minimal_wait (n : ℕ) (positive : 0 < n) :
    ∃ M : ℕ, (∃ c : VirtualHand n, IsMinimalFullWait M c) ∧
      (∀ (m : ℕ) (c : VirtualHand n), IsMinimalFullWait m c → m ≤ M) ∧
        2 * n ≤ M ∧ M < 8 * n :=
  by sorry

theorem alternating_even (a : ℕ) :
    IsFullWait (9 * a + 6) (AlternatingWait.even a) :=
  by sorry

theorem alternating_odd (a : ℕ) :
    IsFullWait (9 * a + 10) (AlternatingWait.odd a) :=
  by sorry

end ComparatorChallenges
