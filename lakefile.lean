import Lake
open System Lake DSL

package yatima where
  srcDir := "src" / "lean4"

@[defaultTarget]
lean_exe yatima where
  root := `Main
