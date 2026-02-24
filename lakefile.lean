import Lake
open Lake DSL

package «logos_library» where
  -- add any package configuration options here
 moreLinkArgs := #["build/midi_interface.o", "-lportmidi"]


require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"



@[default_target]
lean_lib «LogosLibrary» where
moreLinkArgs := #[
    "c/midi_interface.c",  -- Lake will compile this
    "-lportmidi"
  ]
lean_lib MineralCore
lean_lib Level10
  -- add any library configuration options here
