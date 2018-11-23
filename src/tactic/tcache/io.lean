import system.io
open io io.proc

namespace tcache

def CACHE_DIR := ".cache"

def exec_cmd (args : io.process.spawn_args) : io unit := do
let cmdstr := string.intercalate " " (args.cmd :: args.args),
io.put_str_ln $ "> " ++
  match args.cwd with
  | some cwd := cmdstr ++ "    # in directory " ++ cwd
  | none := cmdstr
  end,
ch ← spawn args,
exitv ← wait ch,
when (exitv ≠ 0) $ io.fail $
  "external command exited with status " ++ repr exitv

def mk_cache_dir : io unit :=
  exec_cmd {cmd := "mkdir", args := [CACHE_DIR], stdout := io.process.stdio.null, stderr := io.process.stdio.null}

def file_read (fn : string) : io string := do
  -- mk_cache_dir,
  h ← io.mk_file_handle fn io.mode.read,
  s ← io.fs.read_to_end h,
  io.fs.close h,
  return s.to_string

def file_write (fn : string) (data : string) : io unit := do
  -- mk_cache_dir,
  h ← io.mk_file_handle fn io.mode.write,
  io.fs.write h data.to_char_buffer,
  io.fs.close h

end tcache
