#!/usr/bin/env python3
"""Build Masullo modules from an initialized Mathlib Lake environment."""

import argparse
import os
from graphlib import TopologicalSorter
from pathlib import Path
import subprocess


def main():
    repo = Path(__file__).resolve().parents[1]
    source_root = repo / "src"
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="*", help="Lean module names (default: all library modules)")
    parser.add_argument("--build-dir", type=Path, default=repo / "build" / "lean")
    args = parser.parse_args()
    output = args.build_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)

    env = os.environ.copy()
    for key, path in (("LEAN_SRC_PATH", source_root), ("LEAN_PATH", output)):
        env[key] = os.pathsep.join(filter(None, (str(path), env.get(key))))

    sources = {
        ".".join(path.relative_to(source_root).with_suffix("").parts): path
        for path in sorted(source_root.rglob("*.lean"))
    }
    for name in args.modules:
        if name not in sources:
            parser.error(f"unknown Masullo module {name!r}; use its Lean import name")

    local_sources = set(sources.values())
    dependencies = {}
    pending = [sources[name] for name in args.modules] if args.modules else list(sources.values())
    while pending:
        source = pending.pop()
        if source in dependencies:
            continue
        imports = subprocess.check_output(
            ["lean", "--src-deps", str(source)], text=True, env=env
        ).splitlines()
        dependencies[source] = [Path(path) for path in imports if Path(path) in local_sources]
        pending.extend(dependencies[source])

    def artifact(source):
        return (output / source.relative_to(source_root)).with_suffix(".olean")

    for source in TopologicalSorter(dependencies).static_order():
        target = artifact(source)
        inputs = [source, *(artifact(path) for path in dependencies[source])]
        if target.exists() and all(
            path.stat().st_mtime_ns <= target.stat().st_mtime_ns for path in inputs
        ):
            continue
        print(f"Building {source.relative_to(source_root)}", flush=True)
        target.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            ["lean", f"--root={source_root}", "-o", str(target), str(source)],
            check=True, env=env,
        )


if __name__ == "__main__":
    main()
