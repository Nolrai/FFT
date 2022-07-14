import Lake
open Lake DSL

package fFT {
  -- add package configuration options here
}

lean_lib FFT {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe fFT {
  root := `Main
}
