#!/usr/bin/env python3
"""Download the pinned OMG inputs or verify local copies without network access."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sys
import tempfile
from urllib.request import urlopen

ROOT = Path(__file__).resolve().parents[1]
RAW = ROOT / "sources" / "raw"


def read_manifest():
    entries = json.loads((ROOT / "sources" / "manifest.json").read_text(encoding="utf-8"))
    names = set()
    for entry in entries:
        name = entry["file"]
        if not name or name in {".", ".."} or "/" in name or "\\" in name or name in names:
            raise ValueError(f"invalid or duplicate source filename: {name!r}")
        if not re.fullmatch(r"[0-9a-f]{64}", entry["sha256"]):
            raise ValueError(f"invalid SHA-256 for {name}")
        if not entry["url"].startswith("https://www.omg.org/spec/"):
            raise ValueError(f"unexpected source URL for {name}")
        names.add(name)
    return entries


def verify(entry, path):
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if digest != entry["sha256"]:
        raise ValueError(f"{entry['file']}: expected SHA-256 {entry['sha256']}, got {digest}")


def fetch(entry, directory=RAW, refresh=False):
    directory.mkdir(parents=True, exist_ok=True)
    destination = directory / entry["file"]
    if destination.exists() and not refresh:
        verify(entry, destination)
        return "cached"

    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=directory, prefix=".download-", delete=False) as output:
            temporary = Path(output.name)
            with urlopen(entry["url"], timeout=45) as response:
                shutil.copyfileobj(response, output)
        verify(entry, temporary)
        os.replace(temporary, destination)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
    return "downloaded"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    download = commands.add_parser("fetch", help="download missing files and verify cached files")
    download.add_argument("--refresh", action="store_true", help="download again against the same hashes")
    commands.add_parser("verify", help="check every local file without downloading")
    args = parser.parse_args()

    for entry in read_manifest():
        if args.command == "fetch":
            status = fetch(entry, refresh=args.refresh)
        else:
            verify(entry, RAW / entry["file"])
            status = "verified"
        print(f"{status}: {entry['file']}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print(f"sources: {error}", file=sys.stderr)
        sys.exit(1)
