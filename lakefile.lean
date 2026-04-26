import Lake
open Lake DSL

package «lean-black» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «LeanBlack» where
  srcDir := "."
