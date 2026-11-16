#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
for cmd in bwrap lake lean python3; do
  command -v "$cmd" >/dev/null || { echo "missing required command: $cmd" >&2; exit 1; }
done
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  test -x "$prefix/bin/$tool" || { echo "missing bundled tool: $tool" >&2; exit 1; }
done
config=$(mktemp "${TMPDIR:-/tmp}/palomar-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PYCONFIG'
import json,pathlib,sys
source,dest,prefix=sys.argv[1:]
config=json.loads(pathlib.Path(source).read_text())
if "external_kernels" in config:
    raise SystemExit("Palomar disallows submitter-defined external_kernels")
config.pop("enable_nanoda",None)
config["external_kernels"]={"nanoda":[f"{prefix}/bin/nanoda_bin"],"con-ron":[f"{prefix}/bin/con-ron"]}
pathlib.Path(dest).write_text(json.dumps(config,indent=2)+"\n")
PYCONFIG
lake exe cache get
lake comparator --config "$config"
