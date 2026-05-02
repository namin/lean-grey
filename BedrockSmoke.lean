import LeanBlack.Bedrock

def main : IO Unit := do
  IO.println "Bedrock smoke test..."
  let r ← LeanBlack.Bedrock.invoke LeanBlack.Bedrock.defaultConfig
            "Say the word READY and nothing else."
  match r with
  | .ok text => IO.println s!"OK: {text}"
  | .error e => IO.eprintln s!"ERR: {e}"; IO.Process.exit 1
