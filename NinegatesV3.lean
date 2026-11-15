/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.V3.Hand.Basic
public import Ninegates.V3.Meldable.Virtual
public import Ninegates.V3.Wait.Basic
public import Ninegates.V3.Examples

/-!
# Version 3: formalization of the rewritten paper

The mathematical development starts from integer virtual hands, with independent
order, meld count, and copy bound. The old `Ninegates` target remains available
while the new proof is developed. This target does not import the old finite
enumeration or its classification theorem.
-/
