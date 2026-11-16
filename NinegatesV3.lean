/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.V3.Hand.Basic
public import Ninegates.V3.Meldable.ClosedForm
public import Ninegates.V3.Meldable.SequentialMoving
public import Ninegates.V3.Wait.Basic
public import Ninegates.V3.Wait.TwoPair
public import Ninegates.V3.Wait.Classes
public import Ninegates.V3.Wait.Positive
public import Ninegates.V3.Wait.Bounds
public import Ninegates.V3.Wait.ClassSizes
public import Ninegates.V3.Wait.PillarRemainder
public import Ninegates.V3.Wait.RequiredOne
public import Ninegates.V3.Wait.Reverse
public import Ninegates.V3.Standard.Valid
public import Ninegates.V3.Wait.Abundance
public import Ninegates.V3.Wait.Add
public import Ninegates.V3.Minimal.Maximum
public import Ninegates.V3.Examples
public import Ninegates.V3.MovingExamples
public import Ninegates.V3.GraphExamples
public import Ninegates.V3.SplitExamples
public import Ninegates.V3.BoundsExamples

/-!
# Version 3: formalization of the rewritten paper

The mathematical development starts from integer virtual hands, with independent
order, meld count, and copy bound. The old `Ninegates` target remains available
while the new proof is developed. This target does not import the old finite
enumeration or its classification theorem.
-/
