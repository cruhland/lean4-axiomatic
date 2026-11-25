module
public import Lean4Axiomatic

@[expose] public section

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
