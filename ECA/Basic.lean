module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# The objects of the radius-one block

Three names for the objects every module of the block is about, each an abbreviation, so that a
statement written with the underlying type and a statement written with the name mean the same:

* `ECA.LocalRule` — a local rule of radius one over two states: the value at a cell from its
  left neighbour, itself and its right neighbour;
* `ECA.Configuration` — a configuration of the line: a state at every cell;
* `ECA.FiniteConfiguration` — a finite configuration: a configuration with finitely many cells in
  state `1`, the finitely supported configurations on which the global map of a quiescent rule
  acts.
-/

@[expose] public section

namespace ECA

/-- A local rule of radius one over two states: the value at a cell from its left neighbour, itself
and its right neighbour. -/
abbrev LocalRule := ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2

/-- A configuration of the line: a state at every cell. -/
abbrev Configuration := ℤ → ZMod 2

/-- A finite configuration: a configuration with finitely many cells in state `1`, the finitely
supported configurations on which the global map of a quiescent rule acts. -/
abbrev FiniteConfiguration := ℤ →₀ ZMod 2

end ECA
