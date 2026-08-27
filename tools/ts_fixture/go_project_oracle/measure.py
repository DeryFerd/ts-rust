#!/usr/bin/env python3
"""Run one command and retain its process resource use on Linux."""

import json
from pathlib import Path
import resource
import subprocess
import sys
import time


def main() -> int:
    if len(sys.argv) < 3:
        print("Usage: measure.py OUTPUT COMMAND [ARG ...]", file=sys.stderr)
        return 2
    started = time.monotonic()
    error = None
    try:
        result = subprocess.run(sys.argv[2:], check=False)
        code = result.returncode
        if code < 0:
            code = 128 - code
    except OSError as failure:
        error = str(failure)
        code = 127
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    report = {
        "elapsed_seconds": time.monotonic() - started,
        "peak_rss_kib": usage.ru_maxrss,
        "exit_code": code,
        "error": error,
    }
    Path(sys.argv[1]).write_text(json.dumps(report, sort_keys=True) + "\n")
    return code


if __name__ == "__main__":
    raise SystemExit(main())
