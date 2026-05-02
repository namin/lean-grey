import Lake
open Lake DSL

package «lean-black» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «LeanBlack» where
  srcDir := "."

lean_exe «bedrock-smoke» where
  root := `BedrockSmoke

lean_exe «proposal-smoke» where
  root := `ProposalSmoke

lean_exe «runner» where
  root := `RunnerMain
