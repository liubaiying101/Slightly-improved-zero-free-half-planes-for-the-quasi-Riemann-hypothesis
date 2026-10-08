import Lake
open Lake DSL
package RHZeroFreeExtension where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`warningAsError, true⟩]
require «rellich-kondrachov» from git
  "https://github.com/abenenson/rellich-kondrachov.git" @ "70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23"
require PrimeNumberTheoremAnd from git
  "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.git" @ "c39a751132c88b6e8080b74c74023fd95b3d8be0"
require PrimeCert from git
  "https://github.com/b-mehta/PrimeCert.git" @ "0803c2f6bd289c09704c7d352bb8fcf770cbb9b2"
require leancert from git
  "https://github.com/alerad/leancert.git" @ "7f91b6eb3567437f6cfac03ed279706603ee22f4"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
lean_lib RHZeroFreeExtension

lean_lib OAI where
  srcDir := "vendor"
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`warningAsError, false⟩]

lean_lib geometry
lean_lib analytic_low

post_update pkg do
  for (name, pin, patchName) in #[
      (`«rellich-kondrachov», "70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23", "rellich-kondrachov-lean4341.patch"),
      (`PrimeNumberTheoremAnd, "c39a751132c88b6e8080b74c74023fd95b3d8be0", "PrimeNumberTheoremAnd-lean4341.patch")] do
    let some dep ← findPackageByName? name | error s!"Missing pinned dependency {name}"
    let head ← IO.Process.output { cmd := "git", args := #["-C", dep.dir.toString, "rev-parse", "HEAD"] }
    unless head.exitCode == 0 && head.stdout.trimAscii.toString == pin do
      error s!"Unexpected revision for {name}"
    let patch := pkg.dir / "upstream" / patchName
    let reverse ← IO.Process.output { cmd := "git", args := #["-C", dep.dir.toString,
      "apply", "--check", "--reverse", patch.toString] }
    if reverse.exitCode != 0 then
      let forward ← IO.Process.output { cmd := "git", args := #["-C", dep.dir.toString,
        "apply", "--check", patch.toString] }
      unless forward.exitCode == 0 do
        error s!"Pinned compatibility patch conflicts for {name}: {forward.stderr}"
      let applied ← IO.Process.output { cmd := "git", args := #["-C", dep.dir.toString,
        "apply", patch.toString] }
      unless applied.exitCode == 0 do error s!"Patch failed for {name}: {applied.stderr}"
