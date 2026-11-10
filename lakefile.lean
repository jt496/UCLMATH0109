import Lake
open Lake DSL

package «UCLMATH0109» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    -- don't suggest merging consecutive `intro`s (step-by-step intros are deliberate here)
    ⟨`weak.linter.tacticAnalysis.introMerge, false⟩
  ]
  -- files in this course don't use the module system, so silence the warning about it
  allowNonModules := true
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

@[default_target]
lean_lib «UCLMATH0109» where
  -- add any library configuration options here
