#!/usr/bin/env python3
"""Palomar-oriented static source check; Lean verifies the module headers."""
import os
import re
from pathlib import Path
COMMENT_MARKER = re.compile(r"/-|-/")
ID_LETTER_LIKE = (
    r"\u03b1-\u03ba\u03bc-\u03c9\u0391-\u039f\u03a1-\u03a2\u03a4-\u03a9"
    r"\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
    r"\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u017f"
)
ID_FIRST = rf"A-Za-z_{ID_LETTER_LIKE}"
ID_REST = rf"{ID_FIRST}0-9'!?\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
IDENTIFIER_CONTINUATION = re.compile(rf"[{ID_REST}]|\.[{ID_FIRST}«]")

def has_module_header(text):
    i=0
    while i < len(text):
        if text[i] in " \r\n": i+=1
        elif text.startswith("--",i):
            j=text.find("\n",i+2); i=len(text) if j<0 else j+1
        elif text.startswith("/-",i) and not text.startswith(("/--","/-!"),i):
            i+=3; depth=1
            while depth:
                match=COMMENT_MARKER.search(text,i)
                if match is None: return False
                depth+=1 if match.group()=="/-" else -1
                i=match.end()
        else:
            return text.startswith("module",i) and IDENTIFIER_CONTINUATION.match(text,i+6) is None
    return False

def main():
    root=Path(__file__).resolve().parents[1]
    failed=False
    for folder, subdirs, files in os.walk(root,followlinks=False):
        subdirs[:]=sorted(n for n in subdirs if n not in {".git",".lake"} and not (Path(folder)/n).is_symlink())
        for name in sorted(files):
            if not name.endswith(".lean"): continue
            p=Path(folder)/name
            if p.is_symlink(): print(f"{p.relative_to(root)}: symlink refused");failed=True;continue
            try: text=p.read_bytes().decode("utf-8")
            except UnicodeDecodeError: print(f"{p.relative_to(root)}: not UTF-8");failed=True;continue
            if name!="lakefile.lean" and not has_module_header(text):
                print(f"{p.relative_to(root)}: missing module header");failed=True
            if text.count("\n")+int(bool(text) and not text.endswith("\n"))>10000:
                print(f"{p.relative_to(root)}: over 10,000 lines");failed=True
            if name=="Challenge.lean" and (len(text.encode())>100_000 or len(text.splitlines())>1000):
                print(f"{p.relative_to(root)}: challenge size exceeds limit");failed=True
    if not failed: print("Lean source headers, sizes, symlinks: OK (syntactic precheck)")
    return int(failed)
if __name__=="__main__": raise SystemExit(main())
