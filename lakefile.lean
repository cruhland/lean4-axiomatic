import Lake
open Lake DSL

package «lean4-axiomatic» {
  moreLeanArgs := #["-D warningAsError=true"]
}

lean_lib Lean4Axiomatic {
  -- add library configuration options here
}

@[default_target]
lean_exe «lean4-axiomatic» {
  root := `Main
}
