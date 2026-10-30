module
public import Scripts.OeisIngest.Json

/-!
Packs and restores the compiled `.lake/build` artifacts so that a fresh checkout does not have
to re-elaborate all of `OEISLib`.

    lake exe oeis-cache prune    -- delete regenerable *.setup.json (the bulk of .lake/build)
    lake exe oeis-cache stat     -- report artifact counts and sizes by extension
    lake exe oeis-cache put      -- write cache/loeis-build.tar.zst + cache/manifest.json
    lake exe oeis-cache get      -- restore .lake/build from the archive

Only `lib/` and the `.c` files under `ir/` are archived. `Module.checkArtifactsExist` requires
`.olean`, `.ilean` and `.c` to be present, but never looks at `setup.json`, so those are
dropped: they account for ~94% of the build directory and Lake rewrites them on demand.
-/

namespace Oeis.Cache
public section

structure Config where
  buildDir : System.FilePath := ".lake/build"
  archive : System.FilePath := "cache/loeis-build.tar.zst"
  manifest : System.FilePath := "cache/manifest.json"
  /-- zstd compression level; 6 keeps packing time sane on a ~100 GB tree. -/
  level : Nat := 6
  force : Bool := false

private def run (cmd : String) (args : Array String) : IO Unit := do
  let child ← IO.Process.spawn { cmd, args }
  let rc ← child.wait
  if rc != 0 then
    throw <| IO.userError s!"`{cmd}` exited with code {rc}"

private def readTrimmed (path : System.FilePath) : IO String :=
  return (← IO.FS.readFile path).trimAscii.toString

private def hashFile (path : System.FilePath) : IO String := do
  if ← path.pathExists then
    return Json.toHex (String.hash (← IO.FS.readFile path)).toNat 16
  else
    return ""

/-- `.setup.json` files are inputs Lake regenerates, and they dominate `.lake/build`. -/
partial def pruneDir (dir : System.FilePath) : IO (Nat × Nat) := do
  let mut files := 0
  let mut bytes := 0
  for entry in (← dir.readDir) do
    if ← entry.path.isDir then
      let (f, b) ← pruneDir entry.path
      files := files + f
      bytes := bytes + b
    else if entry.fileName.endsWith ".setup.json" || entry.fileName.endsWith ".setup.json.hash" then
      bytes := bytes + (← entry.path.metadata).byteSize.toNat
      IO.FS.removeFile entry.path
      files := files + 1
  return (files, bytes)

private def fmtBytes (n : Nat) : String :=
  let gb := n.toFloat / 1073741824.0
  if gb ≥ 1.0 then s!"{(gb * 100.0).round / 100.0} GB"
  else s!"{((n.toFloat / 1048576.0) * 100.0).round / 100.0} MB"

private def padRight (w : Nat) (s : String) : String :=
  if s.length ≥ w then s else s ++ String.ofList (List.replicate (w - s.length) ' ')

private def padLeft (w : Nat) (s : String) : String :=
  if s.length ≥ w then s else String.ofList (List.replicate (w - s.length) ' ') ++ s

private def extensionOf (name : String) : String :=
  match (name.splitOn ".").reverse with
  | ext :: _ :: _ => ext
  | _ => "(none)"

partial def statDir (dir : System.FilePath) (acc : Array (String × Nat × Nat)) :
    IO (Array (String × Nat × Nat)) := do
  let mut acc := acc
  for entry in (← dir.readDir) do
    if ← entry.path.isDir then
      acc ← statDir entry.path acc
    else
      let ext := extensionOf entry.fileName
      let size := (← entry.path.metadata).byteSize.toNat
      match acc.findIdx? (fun r => r.1 == ext) with
      | some i =>
        let (_, c, b) := acc[i]!
        acc := acc.set! i (ext, c + 1, b + size)
      | none => acc := acc.push (ext, 1, size)
  return acc

def stat (cfg : Config) : IO Unit := do
  unless ← cfg.buildDir.pathExists do
    throw <| IO.userError s!"no build directory at {cfg.buildDir}"
  let acc ← statDir cfg.buildDir #[]
  let rows := acc.qsort (fun a b => a.2.2 > b.2.2)
  let mut totalFiles := 0
  let mut totalBytes := 0
  IO.println s!"{cfg.buildDir}:"
  for (ext, count, bytes) in rows do
    totalFiles := totalFiles + count
    totalBytes := totalBytes + bytes
    let col := padRight 14 ext
    let num := padLeft 10 (toString count)
    IO.println s!"  {col} {num} files  {fmtBytes bytes}"
  let col := padRight 14 "TOTAL"
  let num := padLeft 10 (toString totalFiles)
  IO.println s!"  {col} {num} files  {fmtBytes totalBytes}"

def prune (cfg : Config) : IO Unit := do
  let ir := cfg.buildDir / "ir"
  unless ← ir.pathExists do
    IO.println s!"nothing to prune: {ir} does not exist"
    return
  let (files, bytes) ← pruneDir ir
  IO.println s!"Pruned {files} setup files, freed {fmtBytes bytes}"

private def writeManifest (cfg : Config) : IO Unit := do
  let size := (← cfg.archive.metadata).byteSize.toNat
  let fields := [
    ("toolchain", Json.str (← readTrimmed "lean-toolchain")),
    ("lakeManifestHash", Json.str (← hashFile "lake-manifest.json")),
    ("lakefileHash", Json.str (← hashFile "lakefile.toml")),
    ("archive", Json.str cfg.archive.toString),
    ("archiveBytes", toString size)
  ]
  let body := fields.map (fun (k, v) => "  " ++ Json.str k ++ ": " ++ v)
  IO.FS.writeFile cfg.manifest ("{\n" ++ String.intercalate ",\n" body ++ "\n}\n")

def put (cfg : Config) : IO Unit := do
  let lib := cfg.buildDir / "lib"
  unless ← lib.pathExists do
    throw <| IO.userError s!"nothing to pack: {lib} does not exist (run `lake build` first)"
  if let some parent := cfg.archive.parent then
    IO.FS.createDirAll parent
  let mut members := #["lib"]
  if ← (cfg.buildDir / "ir").pathExists then
    members := members.push "ir"
  IO.println s!"Packing {members.toList} from {cfg.buildDir} ..."
  -- `--rsyncable` keeps compression-block boundaries stable so Xet/LFS dedup survives a repack.
  run "tar" (#[
    "--use-compress-program", s!"zstd -T0 -{cfg.level} --rsyncable",
    "--exclude=*.setup.json", "--exclude=*.setup.json.hash",
    "-cf", cfg.archive.toString,
    "-C", cfg.buildDir.toString] ++ members)
  writeManifest cfg
  IO.println s!"Wrote {cfg.archive} ({fmtBytes (← cfg.archive.metadata).byteSize.toNat})"
  IO.println s!"Wrote {cfg.manifest}"

private def manifestField (text : String) (key : String) : String :=
  let needle := "\"" ++ key ++ "\": \""
  match (text.splitOn needle).drop 1 |>.head? with
  | none => ""
  | some rest => (rest.splitOn "\"").headD ""

def get (cfg : Config) : IO Unit := do
  unless ← cfg.archive.pathExists do
    throw <| IO.userError s!"no archive at {cfg.archive}"
  if ← cfg.manifest.pathExists then
    let text ← IO.FS.readFile cfg.manifest
    let wantToolchain := manifestField text "toolchain"
    let haveToolchain ← readTrimmed "lean-toolchain"
    let wantLake := manifestField text "lakeManifestHash"
    let haveLake ← hashFile "lake-manifest.json"
    let mismatch :=
      (if wantToolchain != haveToolchain then
        [s!"toolchain: archive={wantToolchain} local={haveToolchain}"] else []) ++
      (if wantLake != haveLake then
        [s!"lake-manifest.json hash: archive={wantLake} local={haveLake}"] else [])
    unless mismatch.isEmpty do
      let msg := "cache does not match this checkout:\n  " ++ String.intercalate "\n  " mismatch
      if cfg.force then
        IO.eprintln s!"warning: {msg}"
      else
        throw <| IO.userError s!"{msg}\nre-run with --force to extract anyway"
  IO.FS.createDirAll cfg.buildDir
  IO.println s!"Extracting {cfg.archive} into {cfg.buildDir} ..."
  run "tar" #[
    "--use-compress-program", "zstd -d -T0",
    "-xf", cfg.archive.toString,
    "-C", cfg.buildDir.toString]
  IO.println "Done. `lake build` should now be a no-op."

def parseArgs (args : List String) : Except String (String × Config) :=
  match args with
  | [] => .error "expected a command: prune, stat, put or get"
  | cmd :: rest =>
    if !["prune", "stat", "put", "get"].contains cmd then
      .error s!"unknown command '{cmd}'"
    else
      (go rest {}).map (fun cfg => (cmd, cfg))
where
  go : List String → Config → Except String Config
    | [], cfg => .ok cfg
    | "--build-dir" :: v :: rest, cfg => go rest { cfg with buildDir := v }
    | "--archive" :: v :: rest, cfg => go rest { cfg with archive := v }
    | "--manifest" :: v :: rest, cfg => go rest { cfg with manifest := v }
    | "--level" :: v :: rest, cfg =>
      match v.toNat? with
      | some n => go rest { cfg with level := n }
      | none => .error s!"--level expects a number, got '{v}'"
    | "--force" :: rest, cfg => go rest { cfg with force := true }
    | arg :: _, _ => .error s!"unrecognized argument '{arg}'"

end
end Oeis.Cache

def main (args : List String) : IO UInt32 := do
  match Oeis.Cache.parseArgs args with
  | .error msg =>
    IO.eprintln s!"error: {msg}"
    IO.eprintln "usage: lake exe oeis-cache <prune|stat|put|get> [--archive PATH] \
      [--manifest PATH] [--build-dir PATH] [--level N] [--force]"
    return 1
  | .ok (cmd, cfg) =>
    match cmd with
    | "prune" => Oeis.Cache.prune cfg
    | "stat" => Oeis.Cache.stat cfg
    | "put" => Oeis.Cache.put cfg
    | "get" => Oeis.Cache.get cfg
    | _ => pure ()
    return 0
