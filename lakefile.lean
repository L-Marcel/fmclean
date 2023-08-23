import Lake
open Lake DSL

package «fmclean1» {
  -- add package configuration options here
}

lean_lib «Defs» {
  -- add library configuration options here
}

@[default_target]
lean_exe «fmclean1» {
  root := `Main
}
