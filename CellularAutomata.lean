/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import CellularAutomata.Accretion
public import CellularAutomata.BlockCount
public import CellularAutomata.Decimation
public import CellularAutomata.DerivedStages
public import CellularAutomata.Doubling
public import CellularAutomata.EndRegionCert
public import CellularAutomata.EndRegionClosure
public import CellularAutomata.EndpointClasses
public import CellularAutomata.GrowingWidth
public import CellularAutomata.HindsightCount
public import CellularAutomata.LightConeWidth
public import CellularAutomata.LocalMargin
public import CellularAutomata.MemoryWidth
public import CellularAutomata.MergeQuotient
public import CellularAutomata.ObservedColumn
public import CellularAutomata.ObservedRays
public import CellularAutomata.ParityEmulation
public import CellularAutomata.PermutiveWidth
public import CellularAutomata.PersistentWord
public import CellularAutomata.PersistentWordCount
public import CellularAutomata.RationalRayBound
public import CellularAutomata.RationalRayLines
public import CellularAutomata.RationalRayPairs
public import CellularAutomata.RationalRayRate
public import CellularAutomata.RationalRayRule90
public import CellularAutomata.RationalRaySeeds
public import CellularAutomata.ReplicationBracket
public import CellularAutomata.WindowCount
public import CellularAutomata.WolframNumber
public import CellularAutomata.AxiomAudit

/-!
# `CellularAutomata`

Elementary cellular automata: the growing kernel, the memory and tap widths of the 256 tables, the
observed columns, the hindsight and window counts, and the rational-ray facts for rule `90`.

This root module imports every module of the library root, including its axiom audit.
-/
